From BusyCoq Require Import Individual62 Longitudinal ES_v3 LongitudinalHalt.
From Coq Require Import Bool List String ZArith Lia btauto.Btauto.
From Coq Require Uint63.

Module XorTree.
Fixpoint tree (n:nat) : Type :=
match n with O => bool | S n => (tree n * tree n)%type end.

Fixpoint add n : tree n -> tree n -> tree n :=
match n with
| O => xorb
| S n => fun x y => (add n (fst x) (fst y), add n (snd x) (snd y))
end.

Fixpoint zeta n : tree n -> tree n :=
match n with
| O => fun x => x
| S n => fun x => let a := zeta n (fst x) in
                  let b := zeta n (snd x) in (add n a b,b)
end.

Fixpoint bits n : tree n -> list bool :=
match n with
| O => fun x => [x]
| S n => fun x => bits n (fst x) ++ bits n (snd x)
end.

Lemma add_assoc n (a b c:tree n):
  add n (add n a b) c = add n a (add n b c).
Proof.
  induction n; cbn [tree] in *.
  - cbn [add]. btauto.
  - destruct a,b,c; cbn [add]; f_equal; apply IHn.
Qed.

Lemma add_swap n (a b c d:tree n):
  add n (add n a b) (add n c d) = add n (add n a c) (add n b d).
Proof.
  induction n; cbn [tree] in *.
  - cbn [add]. btauto.
  - destruct a,b,c,d; cbn [add]; f_equal; apply IHn.
Qed.

Lemma add_cancel n (a b:tree n): add n (add n a b) b = a.
Proof.
  induction n; cbn [tree] in *.
  - cbn [add]. btauto.
  - destruct a,b; cbn [add]; f_equal; apply IHn.
Qed.

Lemma zeta_add n (a b:tree n):
  zeta n (add n a b) = add n (zeta n a) (zeta n b).
Proof.
  induction n; cbn [tree] in *.
  - reflexivity.
  - destruct a,b; cbn [add zeta fst snd].
    rewrite !IHn,add_swap. reflexivity.
Qed.

Lemma zeta_involutive n (a:tree n): zeta n (zeta n a) = a.
Proof.
  induction n; cbn [tree] in *.
  - reflexivity.
  - destruct a; cbn [zeta fst snd].
    rewrite zeta_add,!IHn,add_cancel. reflexivity.
Qed.

Lemma add_cancel_six n (a b c d:tree n):
  add n (add n (add n (add n (add n a b) c) d) c) b = add n a d.
Proof.
  induction n; cbn [tree] in *.
  - cbn [add]. btauto.
  - destruct a,b,c,d; cbn [add]; f_equal; apply IHn.
Qed.
End XorTree.

Module PackedTree.
Import XorTree.
Import PrimInt63.
Local Open Scope uint63_scope.
Local Notation int := Uint63.int.
Local Notation bit := Uint63.bit.
Local Infix "lxor" := Uint63.lxor (at level 40, left associativity).

(* Thirty-two bits fit in a Coq native integer, with power-of-two leaves. *)
Fixpoint read n (i x:int) : XorTree.tree n :=
match n with
| O => bit x i
| S n => (read n i x, read n (Uint63.add i (Uint63.of_Z (Z.of_nat (Nat.pow 2 n)))) x)
end.

Definition zeta32 x :=
  let x := x lxor (Uint63.land (Uint63.lsr x 1) 1431655765) in
  let x := x lxor (Uint63.land (Uint63.lsr x 2) 858993459) in
  let x := x lxor (Uint63.land (Uint63.lsr x 4) 252645135) in
  let x := x lxor (Uint63.land (Uint63.lsr x 8) 16711935) in
  x lxor (Uint63.land (Uint63.lsr x 16) 65535).

Lemma read_xor n i x y:
  read n i (x lxor y) = XorTree.add n (read n i x) (read n i y).
Proof.
  gen i. induction n; cbn [read XorTree.add fst snd]; intros.
  - apply Uint63.lxor_spec.
  - rewrite !IHn. reflexivity.
Qed.

Local Opaque Uint63.bit.
Ltac bit_compute :=
  repeat match goal with
  | |- context [bit (Uint63.lxor ?a ?b) ?i] => rewrite (Uint63.lxor_spec a b i)
  | |- context [bit (Uint63.land ?a ?b) ?i] => rewrite (Uint63.land_spec a b i)
  | |- context [bit (Uint63.lsr ?a ?j) ?i] => rewrite (Uint63.bit_lsr a j i)
  end;
  cbv beta iota zeta delta - [Uint63.bit xorb andb];
  repeat match goal with
  | |- context [bit ?v ?i] =>
    tryif is_var v then fail else
    let r := eval vm_compute in (bit v i) in change (bit v i) with r
  end;
  cbv beta iota zeta delta - [Uint63.bit xorb]; btauto.

Lemma read_zeta32 x: read 5 0 (zeta32 x) = XorTree.zeta 5 (read 5 0 x).
Proof.
  unfold zeta32; cbn [read XorTree.zeta XorTree.add fst snd].
  let rec split_pairs :=
    match goal with |- (_,_) = (_,_) => apply f_equal2; split_pairs | _ => idtac end
  in split_pairs.
  all: abstract bit_compute.
Qed.

Fixpoint tree (n:nat) : Type :=
match n with O => int | S n => (tree n * tree n)%type end.
Fixpoint add n : tree n -> tree n -> tree n :=
match n with
| O => Uint63.lxor
| S n => fun a b => (add n (fst a) (fst b), add n (snd a) (snd b))
end.
Fixpoint zeta n : tree n -> tree n :=
match n with
| O => zeta32
| S n => fun x => let a := zeta n (fst x) in
                  let b := zeta n (snd x) in (add n a b,b)
end.
Fixpoint expand n : tree n -> XorTree.tree (n+5) :=
match n with
| O => fun x => read 5 0 x
| S n => fun x => (expand n (fst x), expand n (snd x))
end.

Lemma expand_add n (a b:tree n):
  expand n (add n a b) = XorTree.add (n+5) (expand n a) (expand n b).
Proof.
  induction n; cbn [tree] in *.
  - apply read_xor.
  - destruct a,b; cbn [expand add XorTree.add fst snd].
    rewrite !IHn. reflexivity.
Qed.

Lemma expand_zeta n (a:tree n):
  expand n (zeta n a) = XorTree.zeta (n+5) (expand n a).
Proof.
  induction n; cbn [tree] in *.
  - apply read_zeta32.
  - destruct a; cbn [expand zeta XorTree.zeta fst snd].
    rewrite expand_add,!IHn. reflexivity.
Qed.

Definition square n (a b:tree n) := (add n a (zeta n b),add n b (zeta n a)).

End PackedTree.

Module PackedEncode.
Import PrimInt63.
Local Open Scope uint63_scope.
Fixpoint encode n : XorTree.tree n -> Uint63.int :=
match n with
| O => Uint63.b2i
| S n => fun x => Uint63.lor (encode n (fst x))
    (Uint63.lsl (encode n (snd x)) (Uint63.of_Z (Z.of_nat (Nat.pow 2 n))))
end.
Local Opaque Uint63.bit.
Lemma encode32_spec x: PackedTree.read 5 0 (encode 5 x) = x.
Proof.
  repeat match goal with x:XorTree.tree (S _) |- _ => destruct x end.
  cbn [encode PackedTree.read fst snd].
  let rec split_pairs :=
    match goal with |- (_,_) = (_,_) => apply f_equal2; split_pairs | _ => idtac end
  in split_pairs.
  all: abstract (
    repeat match goal with
    | |- context [Uint63.bit (Uint63.lor ?a ?b) ?i] => rewrite (Uint63.lor_spec a b i)
    | |- context [Uint63.bit (Uint63.lsl ?a ?j) ?i] => rewrite (Uint63.bit_lsl a j i)
    | |- context [Uint63.bit (Uint63.b2i ?b) ?i] => rewrite (Uint63.bit_b2i b i)
    end;
    cbv beta iota zeta delta - [orb andb]; btauto).
Qed.
End PackedEncode.

(* Normalized digits: true = 0011, false = 1111. *)
Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1RA0LD_1RE0LB_0RC---_1RB1RD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Definition hR (b:bool) := if b then (F,<[1;1;0]) else (C,<[1;1;0]).
Definition hL := (B,[0;0;1]).
Definition h b := [(hR b,hL)].
Definition w (b:bool) := if b then [0;0;1;1] else [1;1;1;1].

Definition left n := 0inf <* <[1;1]^^n.
Lemma init: c0 -->* left 0 {{{(hR false,R)}}} 0inf.
Proof. unfold left,hR. esx. Qed.

Lemma emit n r:
  left n {{{(hL,L)}}} r -->* left (1+n) {{{(hR false,R)}}} r.
Proof. unfold left,hL,hR. es. Qed.

Lemma cell a b:
  segRLs tm (h a) (h (xorb a b)) (w b) (w (xorb a b)).
Proof.
  destruct a,b; apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Qed.

Definition hs := flat_map h.
Definition ws := flat_map w.

Fixpoint sweep a bs :=
match bs with
| [] => (a,[])
| b::bs => let (c,bs') := sweep (xorb a b) bs in
           (c,xorb a b::bs')
end.

Lemma sweep_spec a bs c bs':
  sweep a bs = (c,bs') -> segRLs tm (h a) (h c) (ws bs) (ws bs').
Proof.
  gen a c bs'. induction bs; cbn [sweep]; intros.
  - inverts H. apply segRLs_nil.
  - destruct (sweep (xorb a0 a) bs) as [d ds] eqn:E.
    inverts H. cbn [ws flat_map].
    eapply segRLs_concat; [apply cell|eapply IHbs; eauto].
Qed.

Import XorTree.

(* A square of 2^n calls crossing 2^n cells, in O(n*2^n) operations. *)
Lemma square n (a b:tree n):
  segRLs tm (hs (bits n a)) (hs (bits n (add n a (zeta n b))))
    (ws (bits n b)) (ws (bits n (add n b (zeta n a)))).
Proof.
  gen a b. induction n; intros.
  - destruct a,b; apply cell.
  - destruct a as [a0 a1], b as [b0 b1].
    pose proof (segRLs_trans
      (segRLs_concat (IHn a0 b0) (IHn (add n a0 (zeta n b0)) b1))
      (segRLs_concat (IHn a1 (add n b0 (zeta n a0)))
        (IHn (add n a1 (zeta n (add n b0 (zeta n a0))))
          (add n b1 (zeta n (add n a0 (zeta n b0))))))) as H.
    rewrite !zeta_add,!zeta_involutive in H.
    cbn [bits add zeta fst snd].
    unfold hs,ws in *; rewrite !flat_map_app.
    (* Only XOR cancellation remains; no simulated rows are expanded. *)
    rewrite <- !add_assoc.
    rewrite <- !add_assoc in H.
    rewrite !add_cancel_six in H.
    exact H.
Qed.

Lemma square_packed n (a b:PackedTree.tree n):
  segRLs tm (hs (bits (n+5) (PackedTree.expand n a)))
    (hs (bits (n+5) (PackedTree.expand n
      (PackedTree.add n a (PackedTree.zeta n b)))))
    (ws (bits (n+5) (PackedTree.expand n b)))
    (ws (bits (n+5) (PackedTree.expand n
      (PackedTree.add n b (PackedTree.zeta n a))))).
Proof. rewrite !PackedTree.expand_add,!PackedTree.expand_zeta. apply square. Qed.

Definition packed_bits n (x:PackedTree.tree n) := bits (n+5) (PackedTree.expand n x).

Fixpoint strip T (r:side) : list bool * side :=
match T with
| O => ([],r)
| S T =>
  match r with
  | 0>>0>>1>>1>>r => let (bs,r') := strip T r in (true::bs,r')
  | 1>>1>>1>>1>>r => let (bs,r') := strip T r in (false::bs,r')
  | _ => ([],r)
  end
end.

Lemma strip_spec T r bs r': strip T r = (bs,r') -> r = ws bs *> r'.
Proof.
  gen r bs r'. induction T; intros.
  - inverts H. reflexivity.
  - destruct r as [b0 [b1 [b2 [b3 r]]]].
    destruct b0,b1,b2,b3; cbn [strip] in H;
      try solve [inverts H; reflexivity].
    all: destruct (strip T r) as [ds r0] eqn:E; inverts H;
      apply IHT in E; cbn [ws flat_map w]; rewrite E; reflexivity.
Qed.

(* A failed/budget-exhausted return check is not evidence of halting. *)
Fixpoint halt_rec T (q:Q) (l:list Sym) (r:side) :=
match T with
| O => false
| S T =>
  match r with m>>r =>
    match tm (q,m) with
    | None => true
    | Some (m,R,q) => halt_rec T q (m::l) r
    | Some (m,L,q) =>
      match l with
      | [] => false
      | m'::l => halt_rec T q l (m'>>m>>r)
      end
    end
  end
end.

Lemma halt_rec_spec T q l r:
  halt_rec T q l r = true -> forall l0, halts tm (l0 <* l {{q}}> r).
Proof.
  gen q l r. induction T; cbn [halt_rec]; intros; [congruence|].
  destruct r as [m r]. destruct (tm (q,m)) as [[[m0 []] q0]|] eqn:E.
  - destruct l as [|m' l]; [congruence|].
    eapply halts_step; [|econstructor; apply E].
    cbn. eapply IHT in H. apply H.
  - eapply halts_step; [|econstructor; apply E].
    cbn. eapply IHT in H. apply H.
  - eapply halted_halts,E.
Qed.

Definition edge T a r : (list bool * side) + bool :=
match sideRL_c tm (hR a) hL r T with
| Some r' => inl (strip T r')
| None => inr (halt_rec T (fst (hR a)) (snd (hR a)) r)
end.

Lemma edge_spec T a r:
  match edge T a r with
  | inl (bs,r') => sideRLs tm (h a) r (ws bs *> r')
  | inr true => sideRLs_halt tm (h a) r
  | inr false => True
  end.
Proof.
  unfold edge. destruct (sideRL_c tm (hR a) hL r T) as [r0|] eqn:E.
  - destruct (strip T r0) as [bs r'] eqn:H.
    apply strip_spec in H. subst r0.
    apply sideRL_1. eapply sideRL_c_spec,E.
  - destruct (halt_rec T (fst (hR a)) (snd (hR a)) r) eqn:H; [|trivial].
    constructor. intros l. destruct a; eapply halt_rec_spec,H.
Qed.

Lemma calls_halt k n r:
  sideRLs_halt tm (h false^^k) r -> halts tm (left n {{{(hR false,R)}}} r).
Proof.
  gen n r. induction k; cbn [lpow h app]; intros.
  - inverts H.
  - inversion H as [HR HL hs rr HA|HR HL hs rr rr' HA HB]; subst; clear H.
    + apply HA.
    + eapply halts_evstep; [eapply IHk,HB|].
      eapply evstep_trans; [|apply emit]. eapply progress_evstep,HA.
Qed.

Lemma start_halt k:
  sideRLs_halt tm (h false^^k) 0inf -> halts tm c0.
Proof. intros H. eapply halts_evstep; [eapply calls_halt,H|apply init]. Qed.

Import PrimInt63 PackedEncode.

Definition cast {n m} (e:n=m) (x:PackedTree.tree n) : PackedTree.tree m :=
match e with eq_refl => x end.

(* Fuel bounds only the logarithmic recursion depth, not the tape length. *)
Fixpoint cross fuel n m (a:PackedTree.tree n) (b:PackedTree.tree m)
  : option (PackedTree.tree n * PackedTree.tree m) :=
match fuel with
| O => None
| S fuel =>
  match Nat.eq_dec n m with
  | Coq.Init.Specif.left e => let (a',b') := PackedTree.square n a (cast (eq_sym e) b) in
              Some (a',cast e b')
  | Coq.Init.Specif.right _ =>
    if Nat.leb n m then
      match m as m return PackedTree.tree m -> option (PackedTree.tree n * PackedTree.tree m) with
      | O => fun _ => None
      | S m => fun b =>
        match cross fuel n m a (fst b) with
        | None => None
        | Some (a,b0) =>
          match cross fuel n m a (snd b) with
          | None => None | Some (a,b1) => Some (a,(b0,b1))
          end
        end
      end b
    else
      match n as n return PackedTree.tree n -> option (PackedTree.tree n * PackedTree.tree m) with
      | O => fun _ => None
      | S n => fun a =>
        match cross fuel n m (fst a) b with
        | None => None
        | Some (a0,b) =>
          match cross fuel n m (snd a) b with
          | None => None | Some (a1,b) => Some ((a0,a1),b)
          end
        end
      end a
  end
end.

Lemma cross_spec fuel n m a b a' b':
  cross fuel n m a b = Some (a',b') ->
  segRLs tm (hs (packed_bits n a)) (hs (packed_bits n a'))
    (ws (packed_bits m b)) (ws (packed_bits m b')).
Proof.
  gen n m a b a' b'. induction fuel; cbn [cross]; intros; [congruence|].
  destruct (Nat.eq_dec n m) as [e|e].
  - destruct e. inverts H. apply square_packed.
  - destruct (Nat.leb n m).
    + destruct m; [congruence|]. destruct b as [b0 b1]. cbn [fst snd] in H.
      destruct (cross fuel n m a b0) as [[a0 c0]|] eqn:E0; [|congruence].
      destruct (cross fuel n m a0 b1) as [[a1 c1]|] eqn:E1; [|congruence].
      inverts H. cbn [packed_bits PackedTree.expand XorTree.bits fst snd Nat.add].
      unfold ws; rewrite !flat_map_app.
      eapply segRLs_concat; eapply IHfuel; eauto.
    + destruct n; [congruence|]. destruct a as [a0 a1]. cbn [fst snd] in H.
      destruct (cross fuel n m a0 b) as [[c0 b0]|] eqn:E0; [|congruence].
      destruct (cross fuel n m a1 b0) as [[c1 b1]|] eqn:E1; [|congruence].
      inverts H. cbn [packed_bits PackedTree.expand XorTree.bits fst snd Nat.add].
      unfold hs; rewrite !flat_map_app.
      eapply segRLs_trans; eapply IHfuel; eauto.
Qed.

Inductive block := Block n (x:PackedTree.tree n).
Definition block_bits b := match b with Block n x => packed_bits n x end.
(* The most recently appended block is at the front. *)
Fixpoint forest_bits fs :=
match fs with [] => [] | b::fs => forest_bits fs ++ block_bits b end.

Fixpoint cross_forest fuel n (h:PackedTree.tree n) fs :=
match fs with
| [] => Some (h,[])
| Block m b::fs =>
  match cross_forest fuel n h fs with
  | None => None
  | Some (h,fs) =>
    match cross fuel n m h b with
    | None => None | Some (h,b) => Some (h,Block m b::fs)
    end
  end
end.

Lemma cross_forest_spec fuel n a fs a' fs':
  cross_forest fuel n a fs = Some (a',fs') ->
  segRLs tm (hs (packed_bits n a)) (hs (packed_bits n a'))
    (ws (forest_bits fs)) (ws (forest_bits fs')).
Proof.
  gen a a' fs'. induction fs as [|[m b] fs IH]; cbn [cross_forest]; intros.
  - inverts H. apply segRLs_nil.
  - destruct (cross_forest fuel n a fs) as [[a0 fs0]|] eqn:E0; [|congruence].
    destruct (cross fuel n m a0 b) as [[a1 b1]|] eqn:E1; [|congruence].
    inverts H. cbn [forest_bits block_bits]. unfold ws; rewrite !flat_map_app.
    eapply segRLs_concat; [eapply IH,E0|eapply cross_spec,E1].
Qed.
Fixpoint push fuel (b:block) fs : option (list block) :=
match fuel with
| O => None
| S fuel =>
  match fs with
  | [] => Some [b]
  | Block m y::fs0 =>
    match b with Block n x =>
      match Nat.eq_dec n m with
      | Coq.Init.Specif.left e => push fuel (Block (S n) (cast (eq_sym e) y,x)) fs0
      | Coq.Init.Specif.right _ =>
        if Nat.ltb n m then Some (b::fs) else
        match n as n return PackedTree.tree n -> option (list block) with
        | O => fun _ => None
        | S n => fun x =>
          match push fuel (Block n (fst x)) fs with
          | None => None | Some fs => push fuel (Block n (snd x)) fs
          end
        end x
      end
    end
  end
end.

Lemma push_spec fuel b fs fs':
  push fuel b fs = Some fs' -> forest_bits fs' = forest_bits fs ++ block_bits b.
Proof.
  gen b fs fs'. induction fuel; cbn [push]; intros; [congruence|].
  destruct fs as [|[m y] fs].
  - inverts H. reflexivity.
  - destruct b as [n x]. destruct (Nat.eq_dec n m) as [e|e].
    + destruct e. apply IHfuel in H.
      cbn [forest_bits block_bits packed_bits PackedTree.expand XorTree.bits fst snd Nat.add] in *.
      rewrite H,app_assoc. reflexivity.
    + destruct (Nat.ltb n m).
      * inverts H. reflexivity.
      * destruct n; [congruence|]. destruct x as [x0 x1]. cbn [fst snd] in H.
        destruct (push fuel (Block n x0) (Block m y::fs)) as [fs0|] eqn:E; [|congruence].
        apply IHfuel in H. apply IHfuel in E.
        rewrite H,E. cbn [block_bits packed_bits PackedTree.expand XorTree.bits fst snd Nat.add].
        rewrite app_assoc. reflexivity.
Qed.

Fixpoint append fuel fs gs :=
match gs with
| [] => Some fs
| b::gs => match append fuel fs gs with
           | None => None | Some fs => push fuel b fs end
end.

Lemma append_spec fuel fs gs fs':
  append fuel fs gs = Some fs' -> forest_bits fs' = forest_bits fs ++ forest_bits gs.
Proof.
  gen fs fs'. induction gs; cbn [append forest_bits]; intros.
  - inverts H. rewrite app_nil_r. reflexivity.
  - destruct (append fuel fs gs) as [fs0|] eqn:E; [|congruence].
    apply push_spec in H. apply IHgs in E. rewrite H,E,app_assoc. reflexivity.
Qed.

Fixpoint take n (bs:list bool) : option (XorTree.tree n * list bool) :=
match n with
| O => match bs with [] => None | b::bs => Some (b,bs) end
| S n =>
  match take n bs with
  | None => None
  | Some (a,bs) => match take n bs with
                   | None => None | Some (b,bs) => Some ((a,b),bs) end
  end
end.

Lemma take_spec n bs x rest:
  take n bs = Some (x,rest) -> bs = XorTree.bits n x ++ rest.
Proof.
  gen bs x rest. induction n; cbn [take]; intros.
  - destruct bs; inverts H. reflexivity.
  - destruct (take n bs) as [[a bs0]|] eqn:E0; [|congruence].
    destruct (take n bs0) as [[b bs1]|] eqn:E1; [|congruence].
    inverts H. apply IHn in E0. apply IHn in E1.
    rewrite E0,E1. cbn [XorTree.bits]. rewrite app_assoc. reflexivity.
Qed.

Lemma encoded_bits x: block_bits (Block 0 (encode 5 x)) = XorTree.bits 5 x.
Proof. unfold block_bits,packed_bits. cbn [PackedTree.expand]. rewrite encode32_spec. reflexivity. Qed.

Fixpoint pack fuel rounds bs fs : option (list block * list bool) :=
match rounds with
| O => Some (fs,bs)
| S rounds =>
  match take 5 bs with
  | None => Some (fs,bs)
  | Some (x,rest) =>
    match push fuel (Block 0 (encode 5 x)) fs with
    | None => None | Some fs => pack fuel rounds rest fs end
  end
end.

Lemma pack_spec fuel rounds bs fs fs' rest:
  pack fuel rounds bs fs = Some (fs',rest) ->
  forest_bits fs' ++ rest = forest_bits fs ++ bs.
Proof.
  gen bs fs fs' rest. induction rounds; cbn [pack]; intros.
  - inverts H. reflexivity.
  - destruct (take 5 bs) as [[x bs0]|] eqn:E0.
    + destruct (push fuel (Block 0 (encode 5 x)) fs) as [fs0|] eqn:E1; [|congruence].
      apply IHrounds in H. apply push_spec in E1. apply take_spec in E0.
      rewrite H,E1,encoded_bits,E0,app_assoc. reflexivity.
    + inverts H. reflexivity.
Qed.
Definition one T a bs r : (list bool * side) + bool :=
  let (a,bs0) := sweep a bs in
  match edge T a r with
  | inl (bs1,r) => inl (bs0++bs1,r)
  | inr b => inr b
  end.

Lemma one_spec T a bs r:
  match one T a bs r with
  | inl (bs',r') => sideRLs tm (h a) (ws bs *> r) (ws bs' *> r')
  | inr true => sideRLs_halt tm (h a) (ws bs *> r)
  | inr false => True
  end.
Proof.
  unfold one. destruct (sweep a bs) as [a0 bs0] eqn:E.
  pose proof (edge_spec T a0 r) as H.
  destruct (edge T a0 r) as [[bs1 r1]|[]].
  - unfold ws; rewrite flat_map_app,Str_app_assoc.
    eapply segRLs_sideRLs_concat; [eapply sweep_spec,E|exact H].
  - eapply segRLs_sideRLs_halt_concat; [eapply sweep_spec,E|exact H].
  - trivial.
Qed.

Fixpoint serve T ls bs r : (list bool * side) + bool :=
match ls with
| [] => inl (bs,r)
| a::ls => match one T a bs r with
            | inl (bs,r) => serve T ls bs r | inr b => inr b end
end.

Lemma serve_spec T ls bs r:
  match serve T ls bs r with
  | inl (bs',r') => sideRLs tm (hs ls) (ws bs *> r) (ws bs' *> r')
  | inr true => sideRLs_halt tm (hs ls) (ws bs *> r)
  | inr false => True
  end.
Proof.
  gen bs r. induction ls; intros; cbn [serve].
  - constructor.
  - pose proof (one_spec T a bs r) as H.
    destruct (one T a bs r) as [[bs0 r0]|[]].
    + specialize (IHls bs0 r0). destruct (serve T ls bs0 r0) as [[bs1 r1]|[]].
      * eapply sideRLs_trans; eauto.
      * eapply sideRLs_halt_app_right; eauto.
      * trivial.
    + eapply sideRLs_halt_app_left,H.
    + trivial.
Qed.

(* Consume a dyadic signal stream, retaining only its newly emitted digits.
   The second half must cross the digits emitted by the first half. *)
Fixpoint solve T fuel n (a:PackedTree.tree n) bs r
  : (list block * list bool * side) + bool :=
match n as n return PackedTree.tree n -> (list block * list bool * side) + bool with
| O => fun a =>
    match serve T (packed_bits 0 a) bs r with
    | inl (bs,r) =>
      match pack fuel T bs [] with
      | None => inr false | Some (fs,bs) => inl (fs,bs,r)
      end
    | inr b => inr b
    end
| S n => fun a =>
    match solve T fuel n (fst a) bs r with
    | inr b => inr b
    | inl (fs0,bs0,r0) =>
      match cross_forest fuel n (snd a) fs0 with
      | None => inr false
      | Some (a,fs0) =>
        match solve T fuel n a bs0 r0 with
        | inr b => inr b
        | inl (fs1,bs1,r1) =>
          match append fuel fs0 fs1 with
          | None => inr false | Some fs => inl (fs,bs1,r1)
          end
        end
      end
    end
end a.

Lemma hs_app a b: hs (a++b) = hs a++hs b.
Proof. apply flat_map_app. Qed.
Lemma ws_app a b r: ws (a++b) *> r = ws a *> (ws b *> r).
Proof. unfold ws; rewrite flat_map_app,Str_app_assoc. reflexivity. Qed.
Lemma packed_bits_pair n a b:
  packed_bits (S n) (a,b) = packed_bits n a ++ packed_bits n b.
Proof. reflexivity. Qed.

Lemma solve_spec T fuel n a bs r:
  match solve T fuel n a bs r with
  | inl (fs,bs',r') =>
    sideRLs tm (hs (packed_bits n a)) (ws bs *> r)
      (ws (forest_bits fs++bs') *> r')
  | inr true => sideRLs_halt tm (hs (packed_bits n a)) (ws bs *> r)
  | inr false => True
  end.
Proof.
  gen a bs r. induction n; intros; cbn [solve].
  - pose proof (serve_spec T (packed_bits 0 a) bs r) as H.
    destruct (serve T (packed_bits 0 a) bs r) as [[bs0 r0]|[]]; try trivial.
    destruct (pack fuel T bs0 []) as [[fs bs1]|] eqn:E; [|trivial].
    apply pack_spec in E. cbn [forest_bits app] in E. rewrite E. exact H.
  - destruct a as [a0 a1]. cbn [fst snd].
    rewrite packed_bits_pair,hs_app.
    pose proof (IHn a0 bs r) as H0.
    destruct (solve T fuel n a0 bs r) as [[[fs0 bs0] r0]|[]].
    + destruct (cross_forest fuel n a1 fs0) as [[a2 fs2]|] eqn:E; [|trivial].
      apply cross_forest_spec in E.
      pose proof (IHn a2 bs0 r0) as H1.
      destruct (solve T fuel n a2 bs0 r0) as [[[fs1 bs1] r1]|[]].
      * destruct (append fuel fs2 fs1) as [fs|] eqn:F; [|trivial].
        apply append_spec in F. rewrite F,<-app_assoc,!ws_app.
        rewrite ws_app in H0,H1.
        eapply sideRLs_trans; [exact H0|].
        eapply segRLs_sideRLs_concat; eauto.
      * rewrite ws_app in H0.
        eapply sideRLs_halt_app_right; [exact H0|].
        eapply segRLs_sideRLs_halt_concat; eauto.
      * trivial.
    + eapply sideRLs_halt_app_left,H0.
    + trivial.
Qed.
Fixpoint zero n : PackedTree.tree n :=
match n with O => Uint63.of_Z 0 | S n => let z := zero n in (z,z) end.

Lemma zero_spec n:
  hs (packed_bits n (zero n)) = h false^^(2^(n+5)).
Proof.
  induction n.
  - reflexivity.
  - cbn [zero]. rewrite packed_bits_pair,hs_app,IHn,<-lpow_add.
    f_equal. cbn [Nat.add Nat.pow]. lia.
Qed.

Definition state := (list block * list bool * side)%type.
Definition state_side (c:state) :=
  let '(fs,bs,r) := c in ws (forest_bits fs++bs) *> r.

Definition next T fuel n (c:state) : state+bool :=
  let '(fs,bs,r) := c in
  match cross_forest fuel n (zero n) fs with
  | None => inr false
  | Some (a,fs0) =>
    match solve T fuel n a bs r with
    | inr b => inr b
    | inl (fs1,bs1,r1) =>
      match append fuel fs0 fs1 with
      | None => inr false | Some fs => inl (fs,bs1,r1)
      end
    end
  end.

Lemma next_spec T fuel n c:
  match next T fuel n c with
  | inl c' => sideRLs tm (h false^^(2^(n+5))) (state_side c) (state_side c')
  | inr true => sideRLs_halt tm (h false^^(2^(n+5))) (state_side c)
  | inr false => True
  end.
Proof.
  destruct c as [[fs bs] r]. unfold next.
  destruct (cross_forest fuel n (zero n) fs) as [[a fs0]|] eqn:E; [|trivial].
  apply cross_forest_spec in E. rewrite zero_spec in E.
  pose proof (solve_spec T fuel n a bs r) as H.
  destruct (solve T fuel n a bs r) as [[[fs1 bs1] r1]|[]].
  - destruct (append fuel fs0 fs1) as [fs2|] eqn:F; [|trivial].
    apply append_spec in F. unfold state_side. rewrite F,<-app_assoc,!ws_app.
    rewrite ws_app in H. eapply segRLs_sideRLs_concat; eauto.
  - unfold state_side. rewrite ws_app. eapply segRLs_sideRLs_halt_concat; eauto.
  - trivial.
Qed.

Fixpoint run T fuel n rounds c : state+bool :=
match rounds with
| O => inl c
| S rounds => match next T fuel n c with
              | inl c => run T fuel n rounds c | inr b => inr b end
end.

Lemma run_spec T fuel n rounds c:
  match run T fuel n rounds c with
  | inl c' => sideRLs tm (h false^^(rounds*2^(n+5))) (state_side c) (state_side c')
  | inr true => sideRLs_halt tm (h false^^(rounds*2^(n+5))) (state_side c)
  | inr false => True
  end.
Proof.
  gen c. induction rounds; intros; cbn [run Nat.mul].
  - constructor.
  - rewrite lpow_add. pose proof (next_spec T fuel n c) as H.
    destruct (next T fuel n c) as [c0|[]].
    + specialize (IHrounds c0). destruct (run T fuel n rounds c0) as [c1|[]].
      * eapply sideRLs_trans; eauto.
      * eapply sideRLs_halt_app_right; eauto.
      * trivial.
    + eapply sideRLs_halt_app_left,H.
    + trivial.
Qed.

Definition initial : state := ([],[],0inf).
Definition check T fuel n rounds :=
match run T fuel n rounds initial with inr b => b | inl _ => false end.

Theorem check_spec T fuel n rounds: check T fuel n rounds = true -> halts tm c0.
Proof.
  unfold check. pose proof (run_spec T fuel n rounds initial) as H.
  destruct (run T fuel n rounds initial) as [c|[]]; intros; try discriminate.
  eapply start_halt,H.
Qed.


(* 21 batches of 2^27 calls cover the independently reported halting index.
   Exhausting any local budget returns false, never an assertion of halting. *)
Theorem halt: halts tm c0.
Proof. apply (check_spec 10000 128 22 21). native_check_eq. Qed.

Print Assumptions halt.
End TM1.

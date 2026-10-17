(* 1RB1LE_0RC0LC_1LD0RA_0LA0LF_0LC0LE_0LD--- halts.

   At a left record (state D at the left end) the tape is  0^inf <D W(x0) s0 W(x1) s1 ... W(xn) sn 0^inf
   with W(e) = (10)^e and separators s in {0,1}; we write the list as  x0, x1, ...  with "e," for (e,0)
   and "e|" for (e,1).  x0 is a counter.  Between two records the machine makes one sweep ([Next]): it
   crosses "passive" items (odd commas >= 5) unchanged and rewrites the first other item (the front) and
   a few items after it ([Action]).  An even comma in front of q passive items is carried over all of
   them in 2(1+|q|) sweeps, adding 8 to each ([FF]).  [check] runs this list model, doing such crossings
   in O(1), from the record reached after the first sweep.  Within 1307718 ticks (128477 cycles of the
   counter) the list becomes  x0, P, 23|, 4, 4|  with x0 odd >= 3 and P passive, and that record halts
   ([halt_window]). *)

From BusyCoq Require Import Individual62 ES_v3 Eqb.
Require Import String List Lia NArith.
Import ListNotations.
Set Default Goal Selector "1".

Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC0LC_1LD0RA_0LA0LF_0LC0LE_0LD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* ES_v3 provides es' with at most 3 numbers and 2 sides; threeBars needs 4 and 2. *)
Local Open Scope string_scope.
Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) "&" constr(e) constr(f) :=
  (es_v3_pre; es_v3_nmp_smp
    (fun s => if String.eqb s "a" then a else if String.eqb s "b" then b else
              if String.eqb s "c" then c else if String.eqb s "d" then d else O)
    (fun s => if String.eqb s "e" then e else if String.eqb s "f" then f else 0inf)).
Local Close Scope string_scope.

(** * Local rules of the machine *)

(* crossing a passive item 5+2m: out (state C) and back (state A, then D) *)
Lemma skipR k l r:
  l {{C}}> [1;0] *> [1;0;1;0]^^k *> [0] *> r -->+
  l <* [0] <* [0;0;1;0]^^k <* [0;1] {{C}}> r.
Proof. es' k & l r. Qed.
Lemma skipL m l r:
  l <* [0;1;0;0]^^(2+m) <* [1;0] <{{A}} [0] *> r -->+
  l <{{D}} [1;0] *> [1;0;1;0]^^m *> [0] *> [1;0;1;0;1;0;1;0] *> r.
Proof. es' m & l r. Qed.
Lemma bridgeD l r: l <* [0] <{{D}} r -->+ l <{{A}} [0] *> r.
Proof. es' & l r. Qed.

(* the counter: odd x (3+2n) and x = 1 send C to the first item; even x acts at once *)
Lemma headerR n r:
  0inf {{D}}> [0;1;0] *> [1;0;1;0]^^(1+n) *> [0] *> r -->+
  0inf <* [0;0;1] <* [0;0;1;0]^^(1+n) <* [0;1] {{C}}> r.
Proof. es' n & r. Qed.
Lemma headerL_z n l r:
  l <* [0;0] <* [0;1] <* [0;1;0;0]^^(1+n) <* [1;0] <{{A}} [0] *> r -->+
  l <{{D}} [1;0] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0;1;0;1;0] *> r.
Proof. es' n & l r. Qed.
Lemma headerOneR r:
  0inf {{D}}> [0;1;0;0;1;0;1;0] *> r -->+ 0inf <* [0;1;0;0;0;1;0;0;1] {{C}}> r.
Proof. es' & r. Qed.
Lemma headerOneL r:
  0inf <* [1;0;0;0;1;0;0;1] <{{A}} [0] *> r -->+ 0inf {{D}}> [0;0;0] *> [1;0;1;0;1;0;1;0] *> r.
Proof. es' & r. Qed.
Lemma counterBar_z n l r:
  l <* [0;0;0] {{D}}> [0] *> [1;0;1;0]^^(1+n) *> [1;1] *> r -->+
  l <{{D}} [1;0] *> [1;0;1;0]^^n *> [0;1;0;1;0;1;0;1] *> r.
Proof. es' n & l r. Qed.
Lemma counterZeroBar r: 0inf {{D}}> [0;1;1] *> r -->+ 0inf {{D}}> [0;0;0;1;0;1] *> r.
Proof. es' & r. Qed.
Lemma counterComma_z n l r:
  l <* [0;0;0] {{D}}> [0] *> [1;0;1;0]^^n *> [0;1] *> r -->+
  l <{{D}} [1;0;1;0;1] *> [0;1;0;1]^^n *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma counterMerge_z n l r:
  l <* [0;0;0] {{D}}> [0] *> [1;0;1;0]^^n *> [0;0] *> r -->+
  l <{{D}} [1;0;1;0;1;0] *> [1;0;1;0]^^n *> r.
Proof. es' n & l r. Qed.

(* actions at the front; "head 1" = the next item starts with a 1 *)
Lemma carryA n l r:
  l <* [0] {{C}}> [1;0;1;0]^^n *> [0] *> r -->+ l <{{A}} [0] *> [1] *> [0;1;0;1]^^n *> r.
Proof. es' n & l r. Qed.
Lemma carryHead1 n l r:
  l <* [0] {{C}}> [1;0;1;0]^^(2+n) *> [1;1] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0;1;0] *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma endEven n l:
  l <* [0] {{C}}> [1;0;1;0]^^(2+n) *> [1] *> const 0 -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0;1;0;1;0] *> [1] *> const 0.
Proof. es' n & l. Qed.
Lemma endOdd n l:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^n *> [1] *> const 0 -->+
  l <{{A}} [0] *> [1;0;1;0]^^(1+n) *> [1] *> const 0.
Proof. es' n & l. Qed.
Lemma gadgetOdd a b l r:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^(1+a) *> [1;1;0] *> [1;0;1;0]^^b *> [0;1] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0;1;0] *> [1] *> r.
Proof. es' a b & l r. Qed.
Lemma gadgetLast a b l:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^(1+a) *> [1] *> [1;0;1;0]^^b *> [1] *> const 0 -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0;1;0;1;0] *> [1] *> const 0.
Proof. es' a b & l. Qed.
Lemma gadgetA a b c l r:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^(2+a) *> [1] *> [1;0;1;0]^^(2+b) *> [1;1;0] *>
    [1;0;1;0]^^(2+c) *> [0;1] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^(1+a) *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0]^^(4+c) *> [1] *>
    [1;0;1;0;1;0] *> [1] *> r.
Proof. es' a b c & l r. Qed.
Lemma lastOdd a b l:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^(1+a) *> [1;1;0] *> [1;0;1;0]^^(2+b) *> [1] *> const 0 -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0;1;0;1;0;1;0] *> [0] *>
    [1;0;1;0;1;0;1;0] *> [1] *> const 0.
Proof. es' a b & l. Qed.
Lemma mergeZeroOdd a b l r:
  l <* [0] {{C}}> [1;0;1;0]^^a *> [1;0;1;0] *> [1;0;1;0]^^b *> [0] *> r -->+
  l <{{A}} [0] *> [1;0;1;0]^^(1+a) *> [1;0;1;0]^^b *> [1] *> r.
Proof. es' a b & l r. Qed.
Lemma threeBars a b c d l r:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^(1+a) *> [1] *> [1;0;1;0]^^(2+b) *> [1] *> [1;0;1;0]^^(2+c) *>
    [1;1;0] *> [1;0;1;0]^^d *> [0;1] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0]^^(2+c) *> [1] *>
    [1;0;1;0]^^(2+d) *> [1] *> [1;0;1;0;1;0] *> [1] *> r.
Proof. es' a b c d & l r. Qed.

(* two-sweep gadgets: the first sweep runs to the end of the tape and back *)
Lemma gadgetBR a b l r:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^a *> [1] *> [1;0;1;0]^^(3+b) *> [0] *> r -->+
  l <* [0] <* [0;1;0;0]^^a <* [1;0;0;0]^^(3+b) <* [0;1;0;0] {{C}}> r.
Proof. es' a b & l r. Qed.
Lemma gadgetBTurn a b l r:
  l <* [0] <* [0;1;0;0]^^(1+a) <* [1;0;0;0]^^(3+b) <* [1;0;0] <{{A}} [0] *> r -->+
  l <* [0] <* [0;1;0;0]^^a <* [1;1;0;0] <* [1;0;0;0]^^(1+b) <* [0;1;0;0;0;1;0;0;0;1;0;0] {{C}}> r.
Proof. es' a b & l r. Qed.
Lemma gadgetBL a b l r:
  l <* [0] <* [0;1;0;0]^^a <* [1;1;0;0] <* [1;0;0;0]^^(1+b) <* [1;0;0] <{{A}} [0] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0;1;0;1;0] *> r.
Proof. es' a b & l r. Qed.
Lemma evenCommaR a b c l r:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^a *> [1] *> [1;0;1;0]^^(2+b) *> [1] *> [1;0;1;0]^^(3+c) *> [0] *> r -->+
  l <* [0] <* [0;1;0;0]^^a <* [1;0;0;0]^^(2+b) <* [1;0;0;0;0] <* [1;0;0;0]^^(2+c) <* [0;1;0;0] {{C}}> r.
Proof. es' a b c & l r. Qed.
Lemma evenCommaTurn c l r:
  l <* [1;0;0;0;0] <* [1;0;0;0]^^(2+c) <* [1;0;0] <{{A}} [0] *> r -->+
  l <* [1] <* [1;0;0;0]^^(1+c) <* [0;1;0;0;0;1;0;0;0;1;0;0] {{C}}> r.
Proof. es' c & l r. Qed.
Lemma evenCommaL a b c l r:
  l <* [0] <* [0;1;0;0]^^(1+a) <* [1;0;0;0]^^(2+b) <* [1] <* [1;0;0;0]^^(1+c) <* [1;0;0] <{{A}} [0] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0]^^(2+c) *> [1] *>
    [1;0;1;0;1;0;1;0] *> r.
Proof. es' a b c & l r. Qed.
Lemma twoCommaR a l r:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^a *> [1;1;0;1;0;0] *> r -->+
  l <* [0] <* [0;1;0;0]^^a <* [1;0;0;0] <* [0;1;0;0] {{C}}> r.
Proof. es' a & l r. Qed.
Lemma twoCommaEmptyL a l:
  l <* [0] <* [0;1;0;0]^^(4+a) <* [1;0;0;1;0;0;0] <{{A}} [0] *> [1;0;0;1;0;1;0;1;0;1;0] *> [1] *> const 0 -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0;0;0] *> [1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0] *>
    [0] *> [1;0;1;0;1;0;1;0] *> [1] *> const 0.
Proof. es' a & l. Qed.
Lemma twoCommaL a m l r:
  l <* [0] <* [0;1;0;0]^^(4+a) <* [1;0;0;1;0;0;0] <{{A}} [0] *> [1;0;0;1;0;1;0;1;0;1;0] *> [1;0] *>
    [1;0;1;0]^^m *> [0] *> [1;0;1;0;1;0;1;0] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0;0;0] *> [1;0] *> [1;0;1;0]^^(5+m) *> [0] *>
    [1;0;1;0;1;0;1;0;1;0;1;0;1;0] *> r.
Proof. es' a m & l r. Qed.
Lemma barBR a b l r:
  l <* [0] {{C}}> [1;0] *> [1;0;1;0]^^(2+a) *> [1] *> [1;0;1;0]^^(4+b) *> [1] *> r -->+
  l <* [0] <* [0;1;0;0]^^(2+a) <* [1;0;0;0]^^(5+b) {{B}}> r.
Proof. es' a b & l r. Qed.
Lemma barStep n l r:
  l <* [1;0;0;0] {{B}}> [1;0;1;0]^^(2+n) *> [1] *> r -->+ l <* [1;0;0;0;0] <* [1;0;0;0]^^(2+n) {{B}}> r.
Proof. es' n & l r. Qed.
Lemma barEnd k l:
  l <* [1;0;0;0] {{B}}> [1;0;1;0]^^(2+k) *> [1] *> const 0 -->+
  l <{{E}} [1;0;1;0]^^(2+k) *> [0] *> [1;0;1;0;1;0;1;0] *> [1] *> const 0.
Proof. es' k & l. Qed.
Lemma barBack n m l r:
  l <* [1;0;0;0;0] <* [1;0;0;0]^^(1+n) <{{E}} [1;0;1;0]^^m *> [0] *> r -->+
  l <{{E}} [1;0;1;0]^^n *> [0] *> [1;0;1;0]^^(2+m) *> [1] *> r.
Proof. es' n m & l r. Qed.
Lemma barFinish a b m l r:
  l <* [0] <* [0;1;0;0]^^(2+a) <* [1;0;0;0]^^(4+b) <{{E}} [1;0;1;0]^^m *> [0] *> r -->+
  l <{{A}} [0;1;0] *> [1;0;1;0]^^(1+a) *> [0] *> [1;0;1;0]^^(2+b) *> [0] *> [1;0;1;0]^^(2+m) *> [1] *> r.
Proof. es' a b m & l r. Qed.

(* the halting window 23| 4, 4| *)
Lemma trap23 l :
  halts tm (l {{C}}> [1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1]
                 *> [1;0;1;0;1;0;1;0;0] *> [1;0;1;0;1;0;1;0;1] *> const 0).
Proof. es' & l. Qed.

Lemma zeros2 : 0inf <* [0;0] = 0inf. Proof. solve_const0_eq. Qed.
Lemma zeros3 : 0inf <* [0;0;0] = 0inf. Proof. solve_const0_eq. Qed.
Lemma headerL n r:
  0inf <* [0;1] <* [0;1;0;0]^^(1+n) <* [1;0] <{{A}} [0] *> r -->+
  0inf <{{D}} [1;0] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0;1;0;1;0] *> r.
Proof. rewrite <- zeros2 at 1. apply headerL_z. Qed.
Lemma counterBar n r:
  0inf {{D}}> [0] *> [1;0;1;0]^^(1+n) *> [1;1] *> r -->+
  0inf <{{D}} [1;0] *> [1;0;1;0]^^n *> [0;1;0;1;0;1;0;1] *> r.
Proof. rewrite <- zeros3 at 1. apply counterBar_z. Qed.
Lemma counterComma n r:
  0inf {{D}}> [0] *> [1;0;1;0]^^n *> [0;1] *> r -->+ 0inf <{{D}} [1;0;1;0;1] *> [0;1;0;1]^^n *> [1] *> r.
Proof. rewrite <- zeros3 at 1. apply counterComma_z. Qed.
Lemma counterMerge n r:
  0inf {{D}}> [0] *> [1;0;1;0]^^n *> [0;0] *> r -->+ 0inf <{{D}} [1;0;1;0;1;0] *> [1;0;1;0]^^n *> r.
Proof. rewrite <- zeros3 at 1. apply counterMerge_z. Qed.

(** * The list model *)

Notation item := (nat * bool)%type.
Definition sep (s:bool) : Sym := if s then 1 else 0.
Definition bits (n:nat) : list Sym := [1;0]^^n.
Fixpoint encode (xs:list item) (r:side) : side :=
  match xs with [] => r | (e,s)::xs => bits e *> [sep s] *> encode xs r end.
Definition record (xs:list item) := 0inf <{{D}} encode xs (const 0).
Definition bump (d:nat) (i:item) : item := (d + fst i, snd i).
Definition head1 (i:item) : Prop := (0 < fst i)%nat \/ snd i = true.
Definition credit (r:side) : side := [1;0;1;0;1;0;1;0] *> r.

Lemma bits_add a b : bits (a+b) = bits a ++ bits b.
Proof. apply lpow_add. Qed.
Lemma block_even k : bits (2*k) = [1;0;1;0]^^k.
Proof. unfold bits. replace (2*k)%nat with (k*2)%nat by lia. rewrite lpow_mul. reflexivity. Qed.
Lemma bits_affine c k : bits (c+2*k) = bits c ++ [1;0;1;0]^^k.
Proof. rewrite bits_add, block_even. reflexivity. Qed.
Lemma encode_app xs ys r : encode (xs++ys) r = encode xs (encode ys r).
Proof. induction xs as [|[e s] xs IH]; cbn [encode app]; congruence. Qed.
Lemma encode_cons e s xs r : encode ((e,s)::xs) r = bits e *> [sep s] *> encode xs r.
Proof. reflexivity. Qed.
Lemma bump_encode d h T r : encode (bump d h::T) r = bits d *> encode (h::T) r.
Proof. destruct h as [e s]. cbn [bump encode fst snd]. rewrite bits_add, Str_app_assoc. reflexivity. Qed.
Lemma head1_encode h T r : head1 h -> exists t, encode (h::T) r = [1] *> t.
Proof.
  destruct h as [[|n] s]; cbn [head1 fst snd]; intro H.
  - destruct s; [exists (encode T r); reflexivity|]. destruct H as [H|H]; [cbn in H; exfalso; lia|discriminate].
  - exists ([0] *> bits n *> [sep s] *> encode T r). reflexivity.
Qed.
Lemma rotate01 n r : [1] *> [0;1;0;1]^^n *> r = [1;0;1;0]^^n *> [1] *> r.
Proof. symmetry. apply (lpow_rotate [0;1;0] 1 r n). Qed.
Lemma stack_power (w:list Sym) n m l : l <* w^^n <* w^^m = l <* w^^(n+m).
Proof.
  change (w^^m *> w^^n *> l = w^^(n+m) *> l).
  rewrite <- Str_app_assoc, <- lpow_add. replace (m+n)%nat with (n+m)%nat by lia. reflexivity.
Qed.

(* normal form: fixed offsets expanded, symbolic powers of 1010 kept *)
Ltac norm :=
  cbn [encode sep]; unfold credit; repeat rewrite bits_affine; repeat rewrite block_even;
  cbn [bits lpow app]; repeat rewrite Str_app_assoc; cbn [Str_app].
Tactic Notation "norm" "in" hyp(H) :=
  cbn [encode sep] in H; unfold credit in H; repeat rewrite bits_affine in H;
  repeat rewrite block_even in H; cbn [bits lpow app] in H; repeat rewrite Str_app_assoc in H;
  cbn [Str_app] in H.
Ltac machine H := let K := fresh in pose proof H as K; norm in K; norm; exact K.

(** * Sweeps over passive items 5+2m *)

Fixpoint passive_items (p:list nat) : list item :=
  match p with [] => [] | m::p => ((5+2*m)%nat,false)::passive_items p end.
Fixpoint ptape (p:list nat) (r:side) : side :=
  match p with [] => r | m::p => [1;0] *> [1;0;1;0]^^(2+m) *> [0] *> ptape p r end.
(* the left side after the outward sweep; the return sweep leaves [debit p r] *)
Fixpoint Out (l:side) (p:list nat) : side :=
  match p with [] => l | m::p => Out (l <* [0] <* [0;1;0;0]^^(2+m) <* [1;0]) p end.
Fixpoint debit (p:list nat) (r:side) : side :=
  match p with [] => r | m::p => [1;0] *> [1;0;1;0]^^m *> [0] *> credit (debit p r) end.

Lemma W_rotate k l : l <* [0] <* [0;0;1;0]^^k <* [0;1] = l <* [0;1;0;0]^^k <* [1;0] <* [0].
Proof.
  change ([0;1] *> [0;0;1;0]^^k *> 0 >> l = [0;1;0] *> [0;1;0;0]^^k *> l).
  exact (f_equal (fun x => [0;1] *> x) (lpow_rotate [0;1;0] 0 l k)).
Qed.
Lemma outward_prefix p l r : l <* [0] {{C}}> ptape p r -->* Out l p <* [0] {{C}}> r.
Proof.
  revert l r. induction p as [|m p IH]; intros l r; cbn [Out ptape]; [apply evstep_refl|].
  eapply evstep_trans; [|apply IH]. apply progress_evstep.
  pose proof (skipR (2+m) (l <* [0]) (ptape p r)) as H. rewrite W_rotate in H. exact H.
Qed.
Lemma return_prefix p l r : Out l p <{{A}} [0] *> r -->* l <{{A}} [0] *> debit p r.
Proof.
  revert l r. induction p as [|m p IH]; intros l r; cbn [Out debit]; [apply evstep_refl|].
  eapply evstep_trans; [apply IH|]. apply progress_evstep.
  follow11 (skipL m (l <* [0]) (debit p r)). apply bridgeD.
Qed.
Lemma debit_credit p r : credit (debit p r) = ptape p (credit r).
Proof. induction p as [|m p IH]; cbn [debit ptape]; [reflexivity|]. rewrite <- IH. reflexivity. Qed.
Lemma debit_app p q r : debit (p++q) r = debit p (debit q r).
Proof. induction p as [|m p IH]; cbn [debit app]; congruence. Qed.
Lemma encode_passive p xs r : encode (passive_items p ++ xs) r = ptape p (encode xs r).
Proof. induction p as [|m p IH]; cbn [passive_items encode ptape app]; [reflexivity|]. rewrite IH. norm. reflexivity. Qed.

(* the second sweep of a two-sweep gadget starts with (0010)^2 already rewritten *)
Lemma seeded_outward p l r : p <> [] ->
  l <* [0] <* [0;1;0;0]^^2 {{C}}> debit p r -->+ Out l p <* [0] {{C}}> credit r.
Proof.
  destruct p as [|m p]; intro Hne; [contradiction|]. cbn [debit Out]. rewrite debit_credit.
  pose proof (skipR m (l <* [0] <* [0;1;0;0]^^2) (ptape p (credit r))) as H.
  rewrite W_rotate, stack_power in H.
  eapply progress_evstep_trans; [exact H|apply outward_prefix].
Qed.
Lemma return_even p k l :
  Out l p <* [0] {{C}}> [1;0;1;0]^^(2+k) *> [1] *> const 0 -->+ l <{{A}} [0] *> debit (p++[k]) ([1] *> const 0).
Proof.
  eapply progress_evstep_trans; [apply endEven|].
  rewrite debit_app. exact (return_prefix p l (debit [k] ([1] *> const 0))).
Qed.
Lemma outward_even p k l :
  l <* [0] {{C}}> ptape p ([1;0;1;0]^^(2+k) *> [1] *> const 0) -->+ l <{{A}} [0] *> debit (p++[k]) ([1] *> const 0).
Proof. eapply evstep_progress_trans; [apply outward_prefix|apply return_even]. Qed.

(** * Gadgets that run to the end of the tape *)

Definition B_tail (b:nat) (p:list nat) (k:nat) : list item :=
  ((2*b)%nat,false) :: passive_items p ++ [((5+2*k)%nat,false);(5%nat,false);(4%nat,true)].
Definition BP a b (l:side) : side := l <* [0] <* [0;1;0;0]^^(1+a) <* [1;0;0;0]^^(3+b) <* [1;0;0].
Definition BQ a b (l:side) : side := l <* [0] <* [0;1;0;0]^^a <* [1;1;0;0] <* [1;0;0;0]^^(1+b) <* [1;0;0].
Lemma B_tail_encoding b p k :
  [1;0;1;0]^^b *> [0] *> credit (debit ((p++[k])++[0%nat]) ([1] *> const 0)) = encode (B_tail b p k) (const 0).
Proof. unfold B_tail. rewrite encode_cons, encode_passive, !debit_app, debit_credit. cbn [debit]. norm. reflexivity. Qed.
Lemma gadgetB a b p k l :
  l <* [0] {{C}}> encode (((3+2*a)%nat,true)::((6+2*b)%nat,false)::(passive_items p ++ [((4+2*k)%nat,true)]))
    (const 0) -->+
  l <{{A}} [0] *> bits (1+2*a) *> [0] *> encode (B_tail b p k) (const 0).
Proof.
  eapply progress_trans with (c' := BP a b l <* [0] {{C}}> ptape p ([1;0;1;0]^^(2+k) *> [1] *> const 0)).
  - cbn [encode sep]. rewrite encode_passive. unfold BP.
    machine (gadgetBR (1+a) b l (ptape p ([1;0;1;0]^^(2+k) *> [1] *> const 0))).
  - follow11 (outward_even p k (BP a b l)).
    follow11 (gadgetBTurn a b l (debit (p++[k]) ([1] *> const 0))).
    eapply progress_trans.
    + apply seeded_outward. intro H. apply app_eq_nil in H. destruct H as [_ H]. discriminate.
    + follow11 (return_even (p++[k]) 0 (BQ a b l)).
      rewrite <- B_tail_encoding. machine (gadgetBL a b l (debit ((p++[k])++[0%nat]) ([1] *> const 0))).
Qed.

Fixpoint barred_items (p:list nat) : list item :=
  match p with [] => [] | n::p => ((4+2*n)%nat,true)::barred_items p end.
Fixpoint barred_tape (p:list nat) (r:side) : side :=
  match p with [] => r | n::p => [1;0;1;0]^^(2+n) *> [1] *> barred_tape p r end.
Definition bar_final p k : side := barred_tape p ([1;0;1;0]^^(4+k) *> [1] *> [1;0;1;0;1;0;1;0;1] *> const 0).
Definition bar_residue p k : side :=
  match p with
  | [] => [1;0;1;0]^^(2+k) *> [0] *> [1;0;1;0;1;0;1;0;1] *> const 0
  | n::p => [1;0;1;0]^^n *> [0] *> bar_final p k
  end.
Lemma encode_barred p xs r : encode (barred_items p ++ xs) r = barred_tape p (encode xs r).
Proof. induction p as [|n p IH]; cbn [barred_items encode barred_tape app]; [reflexivity|]. rewrite IH. norm. reflexivity. Qed.
Lemma barred_sweep p k l :
  l <* [1;0;0;0] {{B}}> barred_tape p ([1;0;1;0]^^(2+k) *> [1] *> const 0) -->+ l <{{E}} bar_residue p k.
Proof.
  revert l. induction p as [|n p IH]; intro l; cbn [barred_tape]; [apply barEnd|].
  follow11 (barStep n l (barred_tape p ([1;0;1;0]^^(2+k) *> [1] *> const 0))).
  follow11 (IH (l <* [1;0;0;0;0] <* [1;0;0;0]^^(1+n))).
  destruct p as [|m p]; cbn [bar_residue bar_final barred_tape]; apply barBack.
Qed.
Lemma gadgetBar a b p k l :
  l <* [0] {{C}}> encode (((5+2*a)%nat,true)::((8+2*b)%nat,true)::(barred_items p ++ [((4+2*k)%nat,true)]))
    (const 0) -->+
  l <{{A}} [0] *> encode (((3+2*a)%nat,false)::((4+2*b)%nat,false)::
                          (barred_items p ++ [((8+2*k)%nat,true);(4%nat,true)])) (const 0).
Proof.
  eapply progress_trans with (c' := l <* [0] <* [0;1;0;0]^^(2+a) <* [1;0;0;0]^^(5+b)
    {{B}}> barred_tape p ([1;0;1;0]^^(2+k) *> [1] *> const 0)).
  - cbn [encode sep]. rewrite encode_barred.
    machine (barBR a b l (barred_tape p ([1;0;1;0]^^(2+k) *> [1] *> const 0))).
  - follow11 (barred_sweep p k (l <* [0] <* [0;1;0;0]^^(2+a) <* [1;0;0;0]^^(4+b))).
    cbn [encode sep]. rewrite encode_barred.
    destruct p as [|m p]; cbn [bar_residue bar_final barred_tape].
    + machine (barFinish a b (2+k) l ([1;0;1;0;1;0;1;0;1] *> const 0)).
    + unfold bar_final. machine (barFinish a b m l (bar_final p k)).
Qed.

Definition EC_tail b c p k : list item :=
  ((2*b)%nat,false)::((4+2*c)%nat,true)::(passive_items p ++ [((5+2*k)%nat,false);(5%nat,false);(4%nat,true)]).
Definition ECP a b c (l:side) : side :=
  l <* [0] <* [0;1;0;0]^^(1+a) <* [1;0;0;0]^^(2+b) <* [1;0;0;0;0] <* [1;0;0;0]^^(2+c) <* [1;0;0].
Definition ECQ a b c (l:side) : side :=
  l <* [0] <* [0;1;0;0]^^(1+a) <* [1;0;0;0]^^(2+b) <* [1] <* [1;0;0;0]^^(1+c) <* [1;0;0].
Lemma EC_tail_encoding b c p k :
  [1;0;1;0]^^b *> [0] *> [1;0;1;0]^^(2+c) *> [1] *> credit (debit ((p++[k])++[0%nat]) ([1] *> const 0)) =
  encode (EC_tail b c p k) (const 0).
Proof. unfold EC_tail. rewrite !encode_cons, encode_passive, !debit_app, debit_credit. cbn [debit]. norm. reflexivity. Qed.
Lemma gadgetEC a b c p k l :
  l <* [0] {{C}}> encode (((3+2*a)%nat,true)::((4+2*b)%nat,true)::((6+2*c)%nat,false)::
                          (passive_items p ++ [((4+2*k)%nat,true)])) (const 0) -->+
  l <{{A}} [0] *> bits (1+2*a) *> [0] *> encode (EC_tail b c p k) (const 0).
Proof.
  eapply progress_trans with (c' := ECP a b c l <* [0] {{C}}> ptape p ([1;0;1;0]^^(2+k) *> [1] *> const 0)).
  - rewrite !encode_cons, encode_passive. unfold ECP.
    machine (evenCommaR (1+a) b c l (ptape p ([1;0;1;0]^^(2+k) *> [1] *> const 0))).
  - follow11 (outward_even p k (ECP a b c l)).
    assert (Turn : ECP a b c l <{{A}} [0] *> debit (p++[k]) ([1] *> const 0) -->+
                   ECQ a b c l <* [0] <* [0;1;0;0]^^2 {{C}}> debit (p++[k]) ([1] *> const 0))
      by (unfold ECP, ECQ; apply evenCommaTurn).
    follow11 Turn.
    eapply progress_trans.
    + apply seeded_outward. intro H. apply app_eq_nil in H. destruct H as [_ H]. discriminate.
    + follow11 (return_even (p++[k]) 0 (ECQ a b c l)).
      rewrite <- EC_tail_encoding. machine (evenCommaL a b c l (debit ((p++[k])++[0%nat]) ([1] *> const 0))).
Qed.

Definition TCP a (l:side) : side := l <* [0] <* [0;1;0;0]^^(4+a) <* [1;0;0;1;0;0;0].
Lemma two_start a p k l :
  l <* [0] {{C}}> encode (((9+2*a)%nat,true)::(2%nat,false)::(passive_items p ++ [((4+2*k)%nat,true)])) (const 0) -->+
  TCP a l <{{A}} [0] *> debit (p++[k]) ([1] *> const 0).
Proof.
  eapply progress_trans with (c' := TCP a l <* [0] {{C}}> ptape p ([1;0;1;0]^^(2+k) *> [1] *> const 0)).
  - rewrite !encode_cons, encode_passive. unfold TCP.
    machine (twoCommaR (4+a) l (ptape p ([1;0;1;0]^^(2+k) *> [1] *> const 0))).
  - apply outward_even.
Qed.
Definition seven (p:list nat) (k:nat) : list item :=
  match p with
  | [] => [((8+2*k)%nat,false);(4%nat,true)]
  | m::p => ((8+2*m)%nat,false) :: passive_items p ++ [((5+2*k)%nat,false);(4%nat,true)]
  end.
Lemma seven_encoding p k : bits 7 *> debit (p++[k]) ([1] *> const 0) = encode (seven p k) (const 0).
Proof.
  destruct p as [|m p]; cbn [seven app debit].
  - norm. reflexivity.
  - rewrite debit_app, debit_credit, encode_cons, encode_passive. cbn [debit]. norm. reflexivity.
Qed.
Lemma two_empty a l :
  l <* [0] {{C}}> encode [((9+2*a)%nat,true);(2%nat,false);(4%nat,true)] (const 0) -->+
  l <{{A}} [0] *> bits (1+2*a) *> [0] *> encode [(2%nat,false);(0%nat,false);(11%nat,false);(4%nat,true)] (const 0).
Proof. follow11 (two_start a [] 0 l). unfold TCP. cbn [debit app]. machine (twoCommaEmptyL a l). Qed.
Lemma two_one a k l :
  l <* [0] {{C}}> encode [((9+2*a)%nat,true);(2%nat,false);(5%nat,false);((4+2*k)%nat,true)] (const 0) -->+
  l <{{A}} [0] *> bits (1+2*a) *> [0] *>
    encode [(2%nat,false);(0%nat,false);((11+2*k)%nat,false);(7%nat,true)] (const 0).
Proof. follow11 (two_start a [0%nat] k l). unfold TCP. cbn [debit app]. machine (twoCommaL a k l ([1] *> const 0)). Qed.
Lemma two_many a m p k l :
  l <* [0] {{C}}> encode (((9+2*a)%nat,true)::(2%nat,false)::(5%nat,false)::((5+2*m)%nat,false)::
                          (passive_items p ++ [((4+2*k)%nat,true)])) (const 0) -->+
  l <{{A}} [0] *> bits (1+2*a) *> [0] *> encode ((2%nat,false)::(0%nat,false)::((11+2*m)%nat,false)::seven p k) (const 0).
Proof.
  follow11 (two_start a (0%nat::m::p) k l). rewrite !encode_cons, <- seven_encoding. unfold TCP. cbn [debit app].
  machine (twoCommaL a m l (debit (p++[k]) ([1] *> const 0))).
Qed.

(** * The rules *)

Inductive Action : list item -> list item -> Prop :=
| act_comma n T : Action (((2*n)%nat,false)::T) (((4+2*n)%nat,true)::T)
| act_bar n h T : head1 h -> Action (((4+2*n)%nat,true)::h::T) (((5+2*n)%nat,false)::bump 3 h::T)
| act_end_even n : Action [((4+2*n)%nat,true)] [((5+2*n)%nat,false);(4%nat,true)]
| act_end_odd n : Action [((1+2*n)%nat,true)] [((6+2*n)%nat,true)]
| act_odd a b h T : head1 h ->
    Action (((3+2*a)%nat,true)::((1+2*b)%nat,false)::h::T) (((5+2*a)%nat,false)::((2*b)%nat,false)::bump 3 h::T)
| act_last a b : Action [((3+2*a)%nat,true);((2*b)%nat,true)] [((5+2*a)%nat,false);((2*b)%nat,false);(4%nat,true)]
| act_last_odd a b : Action [((3+2*a)%nat,true);((5+2*b)%nat,true)]
    [((5+2*a)%nat,false);((2*b)%nat,false);(5%nat,false);(4%nat,true)]
| act_A a b c h T : head1 h ->
    Action (((5+2*a)%nat,true)::((4+2*b)%nat,true)::((5+2*c)%nat,false)::h::T)
           (((7+2*a)%nat,false)::((2*b)%nat,false)::((8+2*c)%nat,true)::bump 3 h::T)
| act_three a b c d h T : head1 h ->
    Action (((3+2*a)%nat,true)::((4+2*b)%nat,true)::((4+2*c)%nat,true)::((1+2*d)%nat,false)::h::T)
           (((5+2*a)%nat,false)::((2*b)%nat,false)::((4+2*c)%nat,true)::((4+2*d)%nat,true)::bump 3 h::T)
| act_zero a b T : Action (((2*a)%nat,true)::(0%nat,false)::((1+2*b)%nat,false)::T) (((6+2*a+2*b)%nat,true)::T)
| act_B a b p k : Action (((3+2*a)%nat,true)::((6+2*b)%nat,false)::(passive_items p ++ [((4+2*k)%nat,true)]))
                         (((5+2*a)%nat,false)::B_tail b p k)
| act_bar_tail a b p k :
    Action (((5+2*a)%nat,true)::((8+2*b)%nat,true)::(barred_items p ++ [((4+2*k)%nat,true)]))
           (((7+2*a)%nat,false)::((4+2*b)%nat,false)::(barred_items p ++ [((8+2*k)%nat,true);(4%nat,true)]))
| act_EC a b c p k :
    Action (((3+2*a)%nat,true)::((4+2*b)%nat,true)::((6+2*c)%nat,false)::(passive_items p ++ [((4+2*k)%nat,true)]))
           (((5+2*a)%nat,false)::EC_tail b c p k)
| act_two_empty a : Action [((9+2*a)%nat,true);(2%nat,false);(4%nat,true)]
    [((5+2*a)%nat,false);(2%nat,false);(0%nat,false);(11%nat,false);(4%nat,true)]
| act_two_one a k : Action [((9+2*a)%nat,true);(2%nat,false);(5%nat,false);((4+2*k)%nat,true)]
    [((5+2*a)%nat,false);(2%nat,false);(0%nat,false);((11+2*k)%nat,false);(7%nat,true)]
| act_two_many a m p k :
    Action (((9+2*a)%nat,true)::(2%nat,false)::(5%nat,false)::((5+2*m)%nat,false)::(passive_items p ++ [((4+2*k)%nat,true)]))
           (((5+2*a)%nat,false)::(2%nat,false)::(0%nat,false)::((11+2*m)%nat,false)::seven p k).

(* C enters the front from the left and the machine comes back in state A; the first 8 cells of the
   new list ([credit]) are written later, by the return over the item before the front *)
Definition LocalSound (xs ys:list item) : Prop :=
  forall l, exists r, (l <* [0] {{C}}> encode xs (const 0) -->+ l <{{A}} [0] *> r) /\ credit r = encode ys (const 0).

Lemma Action_sound xs ys : Action xs ys -> LocalSound xs ys.
Proof.
  intro Hact. destruct Hact as [n T | n h T Hh | n | n | a b h T Hh | a b | a b | a b c h T Hh |
    a b c d h T Hh | a b T | a b p k | a b p k | a b c p k | a | a k | a m p k]; intro l;
  try (destruct (head1_encode h T (const 0) Hh) as [r Hr]).
  - exists ([1] *> [0;1;0;1]^^n *> encode T (const 0)). split.
    + cbn [encode sep]. rewrite block_even. apply carryA.
    + unfold credit. cbn [encode sep]. rewrite rotate01. norm. reflexivity.
  - exists ([1;0] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0;1;0;1] *> r). split.
    + rewrite !encode_cons. cbn [sep]. rewrite Hr. machine (carryHead1 n l r).
    + rewrite !encode_cons, bump_encode, Hr. norm. reflexivity.
  - exists ([1;0] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0;1;0;1;0;1] *> const 0).
    split; [machine (endEven n l)|norm; reflexivity].
  - exists ([1;0;1;0]^^(1+n) *> [1] *> const 0). split; [machine (endOdd n l)|norm; reflexivity].
  - exists ([1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0;1;0;1] *> r). split.
    + rewrite !encode_cons. cbn [sep]. rewrite Hr. machine (gadgetOdd a b l r).
    + rewrite !encode_cons, bump_encode, Hr. norm. reflexivity.
  - exists ([1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0;1;0;1;0;1] *> const 0).
    split; [machine (gadgetLast a b l)|norm; reflexivity].
  - exists ([1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0;1;0;1;0;1;0] *> [0] *>
            [1;0;1;0;1;0;1;0;1] *> const 0).
    split; [machine (lastOdd a b l)|norm; reflexivity].
  - exists ([1;0] *> [1;0;1;0]^^(1+a) *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0]^^(4+c) *> [1] *>
            [1;0;1;0;1;0;1] *> r). split.
    + rewrite !encode_cons. cbn [sep]. rewrite Hr. machine (gadgetA a b c l r).
    + rewrite !encode_cons, bump_encode, Hr. norm. reflexivity.
  - exists ([1;0] *> [1;0;1;0]^^a *> [0] *> [1;0;1;0]^^b *> [0] *> [1;0;1;0]^^(2+c) *> [1] *>
            [1;0;1;0]^^(2+d) *> [1] *> [1;0;1;0;1;0;1] *> r). split.
    + rewrite !encode_cons. cbn [sep]. rewrite Hr. machine (threeBars a b c d l r).
    + rewrite !encode_cons, bump_encode, Hr. norm. reflexivity.
  - exists ([1;0;1;0]^^(1+a) *> [1;0;1;0]^^b *> [1] *> encode T (const 0)). split.
    + machine (mergeZeroOdd a b l (encode T (const 0))).
    + unfold credit. cbn [encode sep]. replace (6+2*a+2*b)%nat with (2*(2+((1+a)+b)))%nat by lia.
      rewrite block_even, !lpow_add, !Str_app_assoc. reflexivity.
  - exists (bits (1+2*a) *> [0] *> encode (B_tail b p k) (const 0)). split; [apply gadgetB|norm; reflexivity].
  - exists (encode (((3+2*a)%nat,false)::((4+2*b)%nat,false)::
                    (barred_items p ++ [((8+2*k)%nat,true);(4%nat,true)])) (const 0)).
    split; [apply gadgetBar|norm; reflexivity].
  - exists (bits (1+2*a) *> [0] *> encode (EC_tail b c p k) (const 0)). split; [apply gadgetEC|norm; reflexivity].
  - eexists. split; [apply two_empty|norm; reflexivity].
  - eexists. split; [apply two_one|norm; reflexivity].
  - eexists. split; [apply two_many|norm; reflexivity].
Qed.

Inductive Scan : list item -> list item -> Prop :=
| scan_prefix p xs ys : Action xs ys -> Scan (passive_items p ++ xs) (passive_items p ++ ys).

Lemma Scan_sound xs ys : Scan xs ys -> LocalSound xs ys.
Proof.
  intros [p xs' ys' Hact] l.
  destruct (Action_sound xs' ys' Hact (Out l p)) as [r [Hrun Henc]].
  exists (debit p r). split.
  - rewrite encode_passive. eapply evstep_progress_trans; [apply outward_prefix|].
    eapply progress_evstep_trans; [exact Hrun|apply return_prefix].
  - rewrite debit_credit, Henc. symmetry. apply encode_passive.
Qed.

Definition header_left n : side := 0inf <* [0;1] <* [0;1;0;0]^^(1+n) <* [1;0].
Definition header_one_left : side := 0inf <* [1;0;0;0;1;0;0;1].
Lemma header_out n r : 0inf <{{D}} bits (3+2*n) *> [0] *> r -->+ header_left n <* [0] {{C}}> r.
Proof.
  pose proof (headerR n r) as H.
  change (0inf {{D}}> [0;1;0] *> [1;0;1;0]^^(1+n) *> [0] *> r -->+
          (0inf <* [0;1]) <* [0] <* [0;0;1;0]^^(1+n) <* [0;1] {{C}}> r) in H.
  rewrite W_rotate in H. unfold header_left. norm in H. norm. exact H.
Qed.
Lemma header_one_out n s T :
  record ((1%nat,false)::((2+n)%nat,s)::T) -->+ header_one_left <* [0] {{C}}> encode ((n,s)::T) (const 0).
Proof.
  unfold record, header_one_left. cbn [encode sep]. rewrite bits_add.
  machine (headerOneR (encode ((n,s)::T) (const 0))).
Qed.

Inductive Next : list item -> list item -> Prop :=
| next_odd n xs ys : Scan xs ys -> Next (((3+2*n)%nat,false)::xs) (((1+2*n)%nat,false)::ys)
| next_one n s T ys : Scan ((n,s)::T) ys -> Next ((1%nat,false)::((2+n)%nat,s)::T) ((0%nat,false)::(0%nat,false)::ys)
| next_bar n h T : head1 h -> Next (((2+2*n)%nat,true)::h::T) (((1+2*n)%nat,false)::bump 3 h::T)
| next_zero_bar h T : head1 h -> Next ((0%nat,true)::h::T) ((0%nat,false)::(0%nat,false)::bump 1 h::T)
| next_comma n h T : (0 < fst h)%nat -> Next (((2*n)%nat,false)::h::T) (((2+2*n)%nat,true)::h::T)
| next_merge n h T : Next (((2*n)%nat,false)::(0%nat,false)::h::T) (bump (3+2*n) h::T).

Theorem Next_sound xs ys : Next xs ys -> record xs -->+ record ys.
Proof.
  intro H. destruct H as [n xs ys Hscan | n s T ys Hscan | n h T Hh | h T Hh | n h T Hh | n h T].
  - destruct (Scan_sound xs ys Hscan (header_left n)) as [r [Hrun Henc]].
    unfold record. cbn [encode sep]. follow11 (header_out n (encode xs (const 0))).
    follow11 Hrun. rewrite <- Henc. unfold header_left. machine (headerL n r).
  - destruct (Scan_sound ((n,s)::T) ys Hscan header_one_left) as [r [Hrun Henc]].
    follow11 (header_one_out n s T). follow11 Hrun.
    unfold record. cbn [encode sep bits lpow]. rewrite <- Henc. unfold header_one_left, credit. apply headerOneL.
  - destruct (head1_encode h T (const 0) Hh) as [r Hr].
    change (0inf <{{D}} bits (2+2*n) *> [1] *> encode (h::T) (const 0) -->+
            0inf <{{D}} bits (1+2*n) *> [0] *> encode (bump 3 h::T) (const 0)).
    rewrite bump_encode, Hr. machine (counterBar n r).
  - destruct (head1_encode h T (const 0) Hh) as [r Hr].
    change (0inf <{{D}} [1] *> encode (h::T) (const 0) -->+ 0inf <{{D}} [0;0] *> encode (bump 1 h::T) (const 0)).
    rewrite bump_encode, Hr. machine (counterZeroBar r).
  - destruct (head1_encode h T (const 0) (or_introl Hh)) as [r Hr].
    unfold record. rewrite !encode_cons. cbn [sep]. rewrite Hr.
    pose proof (counterComma n r) as Hrun.
    change (0inf {{D}}> [0] *> [1;0;1;0]^^n *> [0;1] *> r -->+
            0inf <{{D}} [1;0;1;0] *> [1] *> [0;1;0;1]^^n *> [1] *> r) in Hrun.
    rewrite rotate01 in Hrun. norm in Hrun. norm. exact Hrun.
  - unfold record. rewrite bump_encode. cbn [encode sep]. machine (counterMerge n (encode (h::T) (const 0))).
Qed.

(* The fast-forward: the front 2v and the passive run q are carried over in 2(1+|q|) sweeps. *)
Lemma passive_items_app p q : passive_items (p ++ q) = passive_items p ++ passive_items q.
Proof. induction p as [|m p IH]; cbn [passive_items app]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma passive_items_repeat c : passive_items (repeat 0%nat c) = repeat (5%nat, false) c.
Proof. induction c as [|c IH]; cbn [passive_items repeat]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma two_sweeps P v h rest j : head1 h ->
  record (((5 + 2*j)%nat, false) :: passive_items P ++ ((2*v)%nat, false) :: h :: rest) -->+
  record (((1 + 2*j)%nat, false) :: passive_items P ++ ((5 + 2*v)%nat, false) :: bump 3 h :: rest).
Proof.
  intro Hh. eapply progress_trans.
  - apply Next_sound. replace (5 + 2*j)%nat with (3 + 2*(1+j))%nat by lia.
    apply next_odd. apply scan_prefix. apply act_comma.
  - replace (1 + 2*(1+j))%nat with (3 + 2*j)%nat by lia.
    apply Next_sound. apply next_odd. apply scan_prefix. apply act_bar. exact Hh.
Qed.

Lemma FF q : forall P v h rest j, head1 h ->
  record (((4 * (1 + length q) + 1 + 2 * j)%nat, false) :: passive_items P ++
          ((2*v)%nat, false) :: passive_items q ++ h :: rest) -->+
  record (((1 + 2*j)%nat, false) :: passive_items P ++
          ((5 + 2*v)%nat, false) :: passive_items (map (Nat.add 4) q) ++ bump 3 h :: rest).
Proof.
  induction q as [|m q IH]; intros P v h rest j Hh; cbn [length passive_items map app].
  - replace (4 * (1 + 0) + 1 + 2 * j)%nat with (5 + 2*j)%nat by lia. apply two_sweeps. exact Hh.
  - eapply progress_trans.
    + replace (4 * (1 + S (length q)) + 1 + 2 * j)%nat with (5 + 2*(2 * (1 + length q) + j))%nat by lia.
      apply two_sweeps. left. cbn [fst]. lia.
    + replace (1 + 2 * (2 * (1 + length q) + j))%nat with (4 * (1 + length q) + 1 + 2 * j)%nat by lia.
      assert (E : bump 3 ((5 + 2*m)%nat, false) = ((2 * (4 + m))%nat, false))
        by (unfold bump; cbn [fst snd]; f_equal; lia).
      rewrite E. pose proof (IH (P ++ [v]) (4 + m)%nat h rest j Hh) as H.
      rewrite passive_items_app in H. cbn [passive_items app] in H.
      repeat rewrite <- app_assoc in H. cbn [app] in H. exact H.
Qed.

(** * The two ends *)

Lemma init : c0 -->* record [(0%nat,false);(0%nat,false);(3%nat,false);(4%nat,true)].
Proof. unfold record. cbn [encode bits sep lpow app]. execute. Qed.

Lemma halt_window n P :
  halts tm (record (((3 + 2*n)%nat, false) :: passive_items P ++ [(23%nat,true);(4%nat,false);(4%nat,true)])).
Proof.
  unfold record. rewrite encode_cons. cbn [sep]. rewrite encode_passive.
  eapply halts_evstep. 2: { apply progress_evstep. apply header_out. }
  eapply halts_evstep. 2: { apply outward_prefix. }
  exact (trap23 (Out (header_left n) P <* [0])).
Qed.

(** * The checker *)

(* Items with binary values; a block is an item or a run of c items 5, *)
Local Open Scope N_scope.
Definition itN : Type := (N * bool)%type.
Definition toI (i : itN) : item := (N.to_nat (fst i), snd i).
Inductive blk : Type := It (i : itN) | Run (c : N).
Definition flat1 (b : blk) : list item :=
  match b with It i => [toI i] | Run c => repeat (5%nat, false) (N.to_nat c) end.
Fixpoint flat (B : list blk) : list item := match B with [] => [] | b :: B' => flat1 b ++ flat B' end.
Lemma flat_app A B : flat (A ++ B) = flat A ++ flat B.
Proof. induction A as [|b A IH]; cbn [flat app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Definition passN (i : itN) : bool := negb (snd i) && N.odd (fst i) && (5 <=? fst i).
Definition passB (b : blk) : bool := match b with It i => passN i | Run _ => true end.
Definition head1N (i : itN) : bool := (0 <? fst i) || snd i.
Definition mN (i : itN) : nat := N.to_nat (N.div2 (fst i - 5)).
Definition pm1 (b : blk) : list nat := match b with It i => [mN i] | Run c => repeat 0%nat (N.to_nat c) end.
Fixpoint pm (B : list blk) : list nat := match B with [] => [] | b :: B' => pm1 b ++ pm B' end.

Lemma passN_toI i : passN i = true -> toI i = ((5 + 2 * mN i)%nat, false).
Proof.
  destruct i as [v [|]]; unfold passN, toI, mN; cbn [fst snd negb andb]; [discriminate|].
  intro H. apply andb_prop in H as [Ho H5]. apply N.leb_le in H5.
  apply N.odd_spec in Ho as [k ->]. replace (2 * k + 1 - 5) with (2 * (k - 2)) by lia.
  rewrite N.div2_double. f_equal. lia.
Qed.
Lemma passB_flat B : forallb passB B = true -> flat B = passive_items (pm B).
Proof.
  induction B as [|b B IH]; cbn [forallb flat pm]; intro H; [reflexivity|].
  apply andb_prop in H as [Hb HB]. rewrite passive_items_app, (IH HB). f_equal.
  destruct b as [i|c]; cbn [passB flat1 pm1] in *.
  - rewrite (passN_toI i Hb). reflexivity.
  - symmetry. apply passive_items_repeat.
Qed.
Lemma head1N_spec i : head1N i = true -> head1 (toI i).
Proof.
  destruct i as [v s]. unfold head1N, head1, toI. cbn [fst snd].
  intro H. apply Bool.orb_prop in H as [H|H]; [left; apply N.ltb_lt in H; lia|right; exact H].
Qed.
Lemma toI_add d i : toI (d + fst i, snd i) = bump (N.to_nat d) (toI i).
Proof. destruct i as [v s]. unfold toI, bump. cbn [fst snd]. f_equal. lia. Qed.

(* reading one item off the front of a block list *)
Definition run_tail (p : positive) (B : list blk) : list blk :=
  if (p =? 1)%positive then B else Run (N.pos p - 1) :: B.
Lemma run_tail_spec p B : flat (Run (N.pos p) :: B) = (5%nat, false) :: flat (run_tail p B).
Proof.
  unfold run_tail. destruct (p =? 1)%positive eqn:E.
  - apply Pos.eqb_eq in E. subst p. reflexivity.
  - apply Pos.eqb_neq in E.
    change (flat (Run (N.pos p) :: B)) with (repeat (5%nat,false) (N.to_nat (N.pos p)) ++ flat B).
    change (flat (Run (N.pos p - 1) :: B)) with (repeat (5%nat,false) (N.to_nat (N.pos p - 1)) ++ flat B).
    replace (N.to_nat (N.pos p)) with (S (N.to_nat (N.pos p - 1))) by lia. reflexivity.
Qed.
Fixpoint peek (B : list blk) : option (itN * list blk) :=
  match B with
  | [] => None
  | It i :: B' => Some (i, B')
  | Run c :: B' => match c with N0 => peek B' | Npos p => Some ((5, false), run_tail p B') end
  end.
Lemma peek_spec B : forall i B', peek B = Some (i, B') -> flat B = toI i :: flat B'.
Proof.
  induction B as [|b B IH]; intros i B' H; cbn [peek] in H; [discriminate|].
  destruct b as [j|[|p]].
  - injection H as <- <-. reflexivity.
  - exact (IH i B' H).
  - injection H as <- <-. rewrite run_tail_spec. reflexivity.
Qed.
Lemma peek_none B : peek B = None -> flat B = [].
Proof.
  induction B as [|b B IH]; intro H; cbn [peek] in H; [reflexivity|].
  destruct b as [j|[|p]]; [discriminate| |discriminate]. exact (IH H).
Qed.
Lemma peek_passB W i W1 : forallb passB W = true -> peek W = Some (i, W1) -> forallb passB W1 = true.
Proof.
  induction W as [|b W IH]; intros HW H; cbn [peek] in H; [discriminate|].
  cbn [forallb] in HW. apply andb_prop in HW as [Hb HW].
  destruct b as [j|[|p]].
  - injection H as _ <-. exact HW.
  - exact (IH HW H).
  - injection H as _ <-. unfold run_tail. destruct (p =? 1)%positive; [exact HW|]. exact HW.
Qed.
Fixpoint view (k : nat) (W : list blk) : option (list itN * list blk) :=
  match k with
  | O => Some ([], W)
  | S k' => match peek W with
            | Some (i, W1) => match view k' W1 with Some (xs, Rs) => Some (i :: xs, Rs) | None => None end
            | None => None
            end
  end.
Lemma view_spec k : forall W xs Rs, view k W = Some (xs, Rs) -> flat W = map toI xs ++ flat Rs.
Proof.
  induction k as [|k IH]; intros W xs Rs H; cbn [view] in H.
  - injection H as <- <-. reflexivity.
  - destruct (peek W) as [[i W1]|] eqn:E; [|discriminate].
    destruct (view k W1) as [[xs' R']|] eqn:E2; [|discriminate].
    injection H as <- <-. rewrite (peek_spec W i W1 E), (IH W1 xs' R' E2). reflexivity.
Qed.
Definition split_last (W : list blk) : option (list blk * blk) :=
  match rev W with b :: rW => Some (rev rW, b) | [] => None end.
Lemma split_last_spec W U b : split_last W = Some (U, b) -> W = U ++ [b].
Proof.
  unfold split_last. intro H. destruct (rev W) as [|b' rW] eqn:E; [discriminate|].
  injection H as <- <-. rewrite <- (rev_involutive W), E. reflexivity.
Qed.
Definition has_item (W : list blk) : bool := match peek W with Some _ => true | None => false end.
Lemma has_item_false W : negb (has_item W) = true -> flat W = [].
Proof. unfold has_item. destruct (peek W) eqn:E; [discriminate|]. intros _. exact (peek_none W E). Qed.

(* merging adjacent runs of 5s *)
Definition rl (b : blk) : option N :=
  match b with Run c => Some c | It (v, false) => if v =? 5 then Some 1 else None | It _ => None end.
Lemma rl_flat b c : rl b = Some c -> flat1 b = repeat (5%nat, false) (N.to_nat c).
Proof.
  destruct b as [[v [|]]|c']; cbn [rl flat1]; [discriminate| |].
  - destruct (v =? 5) eqn:E; [|discriminate]. intro H. injection H as <-. apply N.eqb_eq in E. subst v. reflexivity.
  - intro H. injection H as <-. reflexivity.
Qed.
Definition cons_blk (b : blk) (C : list blk) : list blk :=
  match rl b with
  | Some c =>
      if c =? 0 then C else
      match C with
      | b2 :: C' => match rl b2 with Some c2 => Run (c + c2) :: C' | None => b :: C end
      | [] => [b]
      end
  | None => b :: C
  end.
Lemma cons_blk_flat b C : flat (cons_blk b C) = flat1 b ++ flat C.
Proof.
  unfold cons_blk. destruct (rl b) as [c|] eqn:Eb; [|reflexivity].
  destruct (c =? 0) eqn:E0.
  - apply N.eqb_eq in E0. subst c. rewrite (rl_flat b 0 Eb). reflexivity.
  - destruct C as [|b2 C']; [reflexivity|]. destruct (rl b2) as [c2|] eqn:E2; [|reflexivity].
    cbn [flat flat1]. rewrite (rl_flat b c Eb), (rl_flat b2 c2 E2), app_assoc, <- repeat_app.
    f_equal. f_equal. lia.
Qed.
Fixpoint canon (B : list blk) : list blk := match B with [] => [] | b :: B' => cons_blk b (canon B') end.
Lemma canon_flat B : flat (canon B) = flat B.
Proof. induction B as [|b B IH]; cbn [canon flat]; [reflexivity|]. rewrite cons_blk_flat, IH. reflexivity. Qed.

(* the rules on binary items *)
Lemma Action_conv xs ys xs' ys' : Action xs ys -> xs = xs' -> ys = ys' -> Action xs' ys'.
Proof. intros H <- <-. exact H. Qed.
Ltac leq :=
  cbn [seven]; unfold toI, bump, B_tail, EC_tail; cbn [fst snd passive_items barred_items app];
  repeat match goal with
  | |- (_ :: _) = (_ :: _) => f_equal
  | |- (_ ++ _) = (_ ++ _) => f_equal
  | |- (_, _) = (_, _) => f_equal
  | |- @eq nat _ _ => lia
  | |- ?x = ?x => reflexivity
  end.
Ltac bfacts :=
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply N.leb_le in H
  | H : head1N _ = true |- _ => apply head1N_spec in H
  end.
Ltac odd x a := apply N.odd_spec in x as [a ->].
Ltac even x a := apply N.even_spec in x as [a ->].

Lemma N_comma v T : N.even v = true -> Action (toI (v,false) :: T) (toI (v+4,true) :: T).
Proof. intros Hv. even Hv a. eapply Action_conv; [apply (act_comma (N.to_nat a))|leq|leq]. Qed.
Lemma N_bar v h T : N.even v = true -> (4 <=? v) = true -> head1N h = true ->
  Action (toI (v,true) :: toI h :: T) (toI (v+1,false) :: toI (3 + fst h, snd h) :: T).
Proof. intros Hv H4 Hh. bfacts. even Hv a. eapply Action_conv; [apply (act_bar (N.to_nat a - 2) _ T Hh)|leq|leq]. Qed.
Lemma N_end_even v : N.even v = true -> (4 <=? v) = true -> Action [toI (v,true)] [toI (v+1,false); toI (4,true)].
Proof. intros Hv H4. bfacts. even Hv a. eapply Action_conv; [apply (act_end_even (N.to_nat a - 2))|leq|leq]. Qed.
Lemma N_end_odd v : N.odd v = true -> Action [toI (v,true)] [toI (v+5,true)].
Proof. intros Hv. odd Hv a. eapply Action_conv; [apply (act_end_odd (N.to_nat a))|leq|leq]. Qed.
Lemma N_odd v u h T : N.odd v = true -> (3 <=? v) = true -> N.odd u = true -> head1N h = true ->
  Action (toI (v,true) :: toI (u,false) :: toI h :: T) (toI (v+2,false) :: toI (u-1,false) :: toI (3 + fst h, snd h) :: T).
Proof.
  intros Hv H3 Hu Hh. bfacts. odd Hv a. odd Hu b.
  eapply Action_conv; [apply (act_odd (N.to_nat a - 1) (N.to_nat b) _ T Hh)|leq|leq].
Qed.
Lemma N_last v u : N.odd v = true -> (3 <=? v) = true -> N.even u = true ->
  Action [toI (v,true); toI (u,true)] [toI (v+2,false); toI (u,false); toI (4,true)].
Proof. intros Hv H3 Hu. bfacts. odd Hv a. even Hu b. eapply Action_conv; [apply (act_last (N.to_nat a - 1) (N.to_nat b))|leq|leq]. Qed.
Lemma N_last_odd v u : N.odd v = true -> (3 <=? v) = true -> N.odd u = true -> (5 <=? u) = true ->
  Action [toI (v,true); toI (u,true)] [toI (v+2,false); toI (u-5,false); toI (5,false); toI (4,true)].
Proof.
  intros Hv H3 Hu H5. bfacts. odd Hv a. odd Hu b.
  eapply Action_conv; [apply (act_last_odd (N.to_nat a - 1) (N.to_nat b - 2))|leq|leq].
Qed.
Lemma N_A v f g h T : N.odd v = true -> (5 <=? v) = true -> N.even f = true -> (4 <=? f) = true ->
  N.odd g = true -> (5 <=? g) = true -> head1N h = true ->
  Action (toI (v,true) :: toI (f,true) :: toI (g,false) :: toI h :: T)
         (toI (v+2,false) :: toI (f-4,false) :: toI (g+3,true) :: toI (3 + fst h, snd h) :: T).
Proof.
  intros Hv H5 Hf H4 Hg H5' Hh. bfacts. odd Hv a. even Hf b. odd Hg c.
  eapply Action_conv; [apply (act_A (N.to_nat a - 2) (N.to_nat b - 2) (N.to_nat c - 2) _ T Hh)|leq|leq].
Qed.
Lemma N_three v f g h i T : N.odd v = true -> (3 <=? v) = true -> N.even f = true -> (4 <=? f) = true ->
  N.even g = true -> (4 <=? g) = true -> N.odd h = true -> head1N i = true ->
  Action (toI (v,true) :: toI (f,true) :: toI (g,true) :: toI (h,false) :: toI i :: T)
         (toI (v+2,false) :: toI (f-4,false) :: toI (g,true) :: toI (h+3,true) :: toI (3 + fst i, snd i) :: T).
Proof.
  intros Hv H3 Hf H4 Hg H4' Hh Hi. bfacts. odd Hv a. even Hf b. even Hg c. odd Hh d.
  eapply Action_conv;
    [apply (act_three (N.to_nat a - 1) (N.to_nat b - 2) (N.to_nat c - 2) (N.to_nat d) _ T Hi)|leq|leq].
Qed.
Lemma N_zero v u T : N.even v = true -> N.odd u = true ->
  Action (toI (v,true) :: toI (0,false) :: toI (u,false) :: T) (toI (v+u+5,true) :: T).
Proof. intros Hv Hu. even Hv a. odd Hu b. eapply Action_conv; [apply (act_zero (N.to_nat a) (N.to_nat b))|leq|leq]. Qed.
Lemma N_B v f U z : N.odd v = true -> (3 <=? v) = true -> N.even f = true -> (6 <=? f) = true ->
  forallb passB U = true -> N.even z = true -> (4 <=? z) = true ->
  Action (toI (v,true) :: toI (f,false) :: flat U ++ [toI (z,true)])
         (toI (v+2,false) :: toI (f-6,false) :: flat U ++ [toI (z+1,false); toI (5,false); toI (4,true)]).
Proof.
  intros Hv H3 Hf H6 HU Hz H4. bfacts. rewrite (passB_flat U HU). odd Hv a. even Hf b. even Hz c.
  eapply Action_conv; [apply (act_B (N.to_nat a - 1) (N.to_nat b - 3) (pm U) (N.to_nat c - 2))|leq|leq].
Qed.
Definition barB (b : blk) : bool := match b with It (u, true) => N.even u && (4 <=? u) | _ => false end.
Definition bm1 (b : blk) : nat := match b with It (u, _) => N.to_nat (N.div2 (u - 4)) | Run _ => 0%nat end.
Lemma barB_flat U : forallb barB U = true -> flat U = barred_items (map bm1 U).
Proof.
  induction U as [|b U IH]; cbn [forallb flat map barred_items]; intro H; [reflexivity|].
  apply andb_prop in H as [Hb HU]. rewrite (IH HU).
  destruct b as [[u [|]]|c]; cbn [barB] in Hb; try discriminate.
  apply andb_prop in Hb as [He H4]. apply N.leb_le in H4. even He k. cbn [flat1 bm1 app]. unfold toI. cbn [fst snd].
  replace (2 * k - 4) with (2 * (k - 2)) by lia. rewrite N.div2_double. f_equal. f_equal. lia.
Qed.
Lemma N_bar_tail v f U z : N.odd v = true -> (5 <=? v) = true -> N.even f = true -> (8 <=? f) = true ->
  forallb barB U = true -> N.even z = true -> (4 <=? z) = true ->
  Action (toI (v,true) :: toI (f,true) :: flat U ++ [toI (z,true)])
         (toI (v+2,false) :: toI (f-4,false) :: flat U ++ [toI (z+4,true); toI (4,true)]).
Proof.
  intros Hv H5 Hf H8 HU Hz H4. bfacts. rewrite (barB_flat U HU). odd Hv a. even Hf b. even Hz c.
  eapply Action_conv; [apply (act_bar_tail (N.to_nat a - 2) (N.to_nat b - 4) (map bm1 U) (N.to_nat c - 2))|leq|leq].
Qed.
Lemma N_EC v f g U z : N.odd v = true -> (3 <=? v) = true -> N.even f = true -> (4 <=? f) = true ->
  N.even g = true -> (6 <=? g) = true -> forallb passB U = true -> N.even z = true -> (4 <=? z) = true ->
  Action (toI (v,true) :: toI (f,true) :: toI (g,false) :: flat U ++ [toI (z,true)])
         (toI (v+2,false) :: toI (f-4,false) :: toI (g-2,true) :: flat U ++ [toI (z+1,false); toI (5,false); toI (4,true)]).
Proof.
  intros Hv H3 Hf H4 Hg H6 HU Hz H4'. bfacts. rewrite (passB_flat U HU). odd Hv a. even Hf b. even Hg c. even Hz d.
  eapply Action_conv;
    [apply (act_EC (N.to_nat a - 1) (N.to_nat b - 2) (N.to_nat c - 3) (pm U) (N.to_nat d - 2))|leq|leq].
Qed.
Lemma N_two_empty v : N.odd v = true -> (9 <=? v) = true ->
  Action [toI (v,true); toI (2,false); toI (4,true)] [toI (v-4,false); toI (2,false); toI (0,false); toI (11,false); toI (4,true)].
Proof. intros Hv H9. bfacts. odd Hv a. eapply Action_conv; [apply (act_two_empty (N.to_nat a - 4))|leq|leq]. Qed.
Lemma N_two_one v z : N.odd v = true -> (9 <=? v) = true -> N.even z = true -> (4 <=? z) = true ->
  Action [toI (v,true); toI (2,false); toI (5,false); toI (z,true)]
         [toI (v-4,false); toI (2,false); toI (0,false); toI (z+7,false); toI (7,true)].
Proof. intros Hv H9 Hz H4. bfacts. odd Hv a. even Hz c. eapply Action_conv; [apply (act_two_one (N.to_nat a - 4) (N.to_nat c - 2))|leq|leq]. Qed.
Lemma N_two_many_nil v w z : N.odd v = true -> (9 <=? v) = true -> N.odd w = true -> (5 <=? w) = true ->
  N.even z = true -> (4 <=? z) = true ->
  Action [toI (v,true); toI (2,false); toI (5,false); toI (w,false); toI (z,true)]
         [toI (v-4,false); toI (2,false); toI (0,false); toI (w+6,false); toI (z+4,false); toI (4,true)].
Proof.
  intros Hv H9 Hw H5 Hz H4. bfacts. odd Hv a. odd Hw m. even Hz c.
  eapply Action_conv; [apply (act_two_many (N.to_nat a - 4) (N.to_nat m - 2) [] (N.to_nat c - 2))|leq|leq].
Qed.
Lemma N_two_many_cons v w w2 U z : N.odd v = true -> (9 <=? v) = true -> N.odd w = true -> (5 <=? w) = true ->
  N.odd w2 = true -> (5 <=? w2) = true -> forallb passB U = true -> N.even z = true -> (4 <=? z) = true ->
  Action (toI (v,true) :: toI (2,false) :: toI (5,false) :: toI (w,false) :: toI (w2,false) :: flat U ++ [toI (z,true)])
         (toI (v-4,false) :: toI (2,false) :: toI (0,false) :: toI (w+6,false) :: toI (w2+3,false) ::
            flat U ++ [toI (z+1,false); toI (4,true)]).
Proof.
  intros Hv H9 Hw H5 Hw2 H5' HU Hz H4. bfacts. rewrite (passB_flat U HU). odd Hv a. odd Hw m. odd Hw2 m2. even Hz c.
  eapply Action_conv;
    [apply (act_two_many (N.to_nat a - 4) (N.to_nat m - 2) ((N.to_nat m2 - 2)%nat :: pm U) (N.to_nat c - 2))|leq|leq].
Qed.

(* rule matching on block lists *)
Lemma some_inj {A : Type} (x y : A) : Some x = Some y -> x = y.
Proof. congruence. Qed.
Ltac sinj H := apply some_inj in H; subst.
Ltac dsimpl H :=
  repeat (match type of H with
          | context [ match ?x with _ => _ end ] => first [ is_var x; destruct x | destruct x eqn:? ]
          end; try discriminate H).
Ltac bsplit := repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H; destruct H end.
Ltac use_views :=
  repeat match goal with
  | E : peek ?W = Some (?i, ?W') |- _ => rewrite (peek_spec W i W' E) in *; clear E
  | E : view ?k ?W = Some (?xs, ?R) |- _ => rewrite (view_spec k W xs R E) in *; clear E
  | E : split_last ?W = Some (?U, ?b) |- _ => rewrite (split_last_spec W U b E) in *; clear E
  | E : peek ?W = None |- _ => rewrite (peek_none W E) in *; clear E
  end.
Ltac fnorm := repeat rewrite flat_app; cbn [flat flat1 map app].
Ltac rule_tac f := intros W W' H; unfold f in H; dsimpl H; sinj H; bsplit;
  repeat match goal with Hz : (?z =? _) = true |- _ => apply N.eqb_eq in Hz; subst z end;
  do 3 (fnorm; use_views); fnorm.

Definition WinOK (f : list blk -> option (list blk)) : Prop := forall W W', f W = Some W' -> Action (flat W) (flat W').

Definition g_comma (W : list blk) : option (list blk) :=
  match W with It (v, false) :: W1 => if N.even v then Some (It (v+4, true) :: W1) else None | _ => None end.
Lemma g_comma_ok : WinOK g_comma.
Proof. rule_tac g_comma. apply N_comma; assumption. Qed.
Definition g_bar (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match peek W1 with
      | Some (h, W2) => if N.even v && (4 <=? v) && head1N h then Some (It (v+1,false) :: It (3 + fst h, snd h) :: W2) else None
      | None => None
      end
  | _ => None
  end.
Lemma g_bar_ok : WinOK g_bar.
Proof. rule_tac g_bar. apply N_bar; assumption. Qed.
Definition g_zero (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match view 2 W1 with
      | Some ([(z, false); (u, false)], W3) => if N.even v && (z =? 0) && N.odd u then Some (It (v+u+5, true) :: W3) else None
      | _ => None
      end
  | _ => None
  end.
Lemma g_zero_ok : WinOK g_zero.
Proof. rule_tac g_zero. apply N_zero; assumption. Qed.
Definition g_odd (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match view 2 W1 with
      | Some ([(u, false); h], W3) =>
          if N.odd v && (3 <=? v) && N.odd u && head1N h
          then Some (It (v+2,false) :: It (u-1,false) :: It (3 + fst h, snd h) :: W3) else None
      | _ => None
      end
  | _ => None
  end.
Lemma g_odd_ok : WinOK g_odd.
Proof. rule_tac g_odd. apply N_odd; assumption. Qed.
Definition g_A (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match view 3 W1 with
      | Some ([(f, true); (g, false); h], W4) =>
          if N.odd v && (5 <=? v) && N.even f && (4 <=? f) && N.odd g && (5 <=? g) && head1N h
          then Some (It (v+2,false) :: It (f-4,false) :: It (g+3,true) :: It (3 + fst h, snd h) :: W4) else None
      | _ => None
      end
  | _ => None
  end.
Lemma g_A_ok : WinOK g_A.
Proof. rule_tac g_A. apply N_A; assumption. Qed.
Definition g_three (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match view 4 W1 with
      | Some ([(f, true); (g, true); (h, false); i], W5) =>
          if N.odd v && (3 <=? v) && N.even f && (4 <=? f) && N.even g && (4 <=? g) && N.odd h && head1N i
          then Some (It (v+2,false) :: It (f-4,false) :: It (g,true) :: It (h+3,true) :: It (3 + fst i, snd i) :: W5)
          else None
      | _ => None
      end
  | _ => None
  end.
Lemma g_three_ok : WinOK g_three.
Proof. rule_tac g_three. apply N_three; assumption. Qed.
Definition e_single (W : list blk) : option (list blk) :=
  match W with
  | [It (v, true)] =>
      if N.even v && (4 <=? v) then Some [It (v+1,false); It (4,true)]
      else if N.odd v then Some [It (v+5,true)] else None
  | _ => None
  end.
Lemma e_single_ok : WinOK e_single.
Proof. rule_tac e_single; [apply N_end_even|apply N_end_odd]; assumption. Qed.
Definition e_pair (W : list blk) : option (list blk) :=
  match W with
  | [It (v, true); It (u, true)] =>
      if N.odd v && (3 <=? v) && N.even u then Some [It (v+2,false); It (u,false); It (4,true)]
      else if N.odd v && (3 <=? v) && N.odd u && (5 <=? u)
      then Some [It (v+2,false); It (u-5,false); It (5,false); It (4,true)] else None
  | _ => None
  end.
Lemma e_pair_ok : WinOK e_pair.
Proof. rule_tac e_pair; [apply N_last|apply N_last_odd]; assumption. Qed.
Definition e_B (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match peek W1 with
      | Some ((f, false), W2) =>
          if N.odd v && (3 <=? v) && N.even f && (6 <=? f) then
            match split_last W2 with
            | Some (U, It (z, true)) =>
                if forallb passB U && N.even z && (4 <=? z)
                then Some (It (v+2,false) :: It (f-6,false) :: U ++ [It (z+1,false); It (5,false); It (4,true)]) else None
            | _ => None
            end
          else None
      | _ => None
      end
  | _ => None
  end.
Lemma e_B_ok : WinOK e_B.
Proof. rule_tac e_B. apply N_B; assumption. Qed.
Definition e_bar_tail (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match peek W1 with
      | Some ((f, true), W2) =>
          if N.odd v && (5 <=? v) && N.even f && (8 <=? f) then
            match split_last W2 with
            | Some (U, It (z, true)) =>
                if forallb barB U && N.even z && (4 <=? z)
                then Some (It (v+2,false) :: It (f-4,false) :: U ++ [It (z+4,true); It (4,true)]) else None
            | _ => None
            end
          else None
      | _ => None
      end
  | _ => None
  end.
Lemma e_bar_tail_ok : WinOK e_bar_tail.
Proof. rule_tac e_bar_tail. apply N_bar_tail; assumption. Qed.
Definition e_EC (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      match view 2 W1 with
      | Some ([(f, true); (g, false)], W3) =>
          if N.odd v && (3 <=? v) && N.even f && (4 <=? f) && N.even g && (6 <=? g) then
            match split_last W3 with
            | Some (U, It (z, true)) =>
                if forallb passB U && N.even z && (4 <=? z)
                then Some (It (v+2,false) :: It (f-4,false) :: It (g-2,true) ::
                           U ++ [It (z+1,false); It (5,false); It (4,true)])
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  | _ => None
  end.
Lemma e_EC_ok : WinOK e_EC.
Proof. rule_tac e_EC. apply N_EC; assumption. Qed.
Definition e_two (W : list blk) : option (list blk) :=
  match W with
  | It (v, true) :: W1 =>
      if N.odd v && (9 <=? v) then
      match peek W1 with
      | Some ((t, false), W2) =>
          if t =? 2 then
          match peek W2 with
          | Some ((z, true), W3) =>
              if (z =? 4) && negb (has_item W3)
              then Some [It (v-4,false); It (2,false); It (0,false); It (11,false); It (4,true)] else None
          | Some ((f5, false), W3) =>
              if f5 =? 5 then
              match peek W3 with
              | Some ((z, true), W4) =>
                  if N.even z && (4 <=? z) && negb (has_item W4)
                  then Some [It (v-4,false); It (2,false); It (0,false); It (z+7,false); It (7,true)] else None
              | Some ((w, false), W4) =>
                  if N.odd w && (5 <=? w) then
                  match split_last W4 with
                  | Some (U, It (z, true)) =>
                      if forallb passB U && N.even z && (4 <=? z) then
                      match peek U with
                      | None => Some [It (v-4,false); It (2,false); It (0,false); It (w+6,false); It (z+4,false); It (4,true)]
                      | Some ((w2, false), U2) =>
                          if N.odd w2 && (5 <=? w2)
                          then Some (It (v-4,false) :: It (2,false) :: It (0,false) :: It (w+6,false) ::
                                     It (w2+3,false) :: U2 ++ [It (z+1,false); It (4,true)])
                          else None
                      | _ => None
                      end
                      else None
                  | _ => None
                  end
                  else None
              | _ => None
              end
              else None
          | _ => None
          end
          else None
      | _ => None
      end
      else None
  | _ => None
  end.
Lemma e_two_ok : WinOK e_two.
Proof.
  intros W W' H. unfold e_two in H. dsimpl H; sinj H; bsplit;
  repeat match goal with
  | Hz : (?z =? _) = true |- _ => apply N.eqb_eq in Hz; subst z
  | Hn : negb (has_item ?W) = true |- _ => apply has_item_false in Hn
  | E : peek ?U = Some (?i, ?U2), HU : forallb passB ?U = true |- _ =>
      lazymatch goal with _ : forallb passB U2 = true |- _ => fail | _ => pose proof (peek_passB U i U2 HU E) end
  end;
  do 3 (fnorm; use_views); fnorm;
  repeat match goal with Hn : flat ?W = [] |- _ => rewrite Hn in *; clear Hn end; cbn [app];
  first [ apply N_two_empty; assumption | apply N_two_one; assumption
        | apply N_two_many_nil; assumption | apply N_two_many_cons; assumption ].
Qed.

Fixpoint first_some {A B : Type} (fs : list (A -> option B)) (x : A) : option B :=
  match fs with [] => None | f :: fs => match f x with Some y => Some y | None => first_some fs x end end.
Lemma first_some_spec {A B : Type} (P : A -> B -> Prop) fs x y :
  Forall (fun f => forall x y, f x = Some y -> P x y) fs -> first_some fs x = Some y -> P x y.
Proof.
  intro HF. induction HF as [|f fs Hf _ IH]; cbn [first_some]; [discriminate|].
  destruct (f x) eqn:E; [intro H; injection H as <-; exact (Hf x _ E)|exact IH].
Qed.

Definition window : list blk -> option (list blk) :=
  first_some [g_comma; g_bar; g_zero; g_odd; g_A; g_three; e_single; e_pair; e_two; e_B; e_bar_tail; e_EC].
Lemma window_ok : WinOK window.
Proof.
  intros W W'. apply (first_some_spec (fun W W' => Action (flat W) (flat W'))).
  repeat constructor;
  [ exact g_comma_ok | exact g_bar_ok | exact g_zero_ok | exact g_odd_ok | exact g_A_ok | exact g_three_ok
  | exact e_single_ok | exact e_pair_ok | exact e_two_ok | exact e_B_ok | exact e_bar_tail_ok | exact e_EC_ok ].
Qed.

Definition halt_pat (W : list blk) : bool :=
  match W with
  | [It (a, true); It (b, false); It (c, true)] => (a =? 23) && (b =? 4) && (c =? 4)
  | _ => false
  end.
Lemma halt_pat_spec W : halt_pat W = true -> flat W = [(23%nat,true);(4%nat,false);(4%nat,true)].
Proof.
  intro H. unfold halt_pat in H. dsimpl H. bsplit.
  repeat match goal with Hz : (?z =? _) = true |- _ => apply N.eqb_eq in Hz; subst z end. reflexivity.
Qed.

(* one sweep: cross the passive prefix and act on the window from the front to the end *)
Fixpoint split_pass (T : list blk) : option (list blk * list blk) :=
  match T with
  | [] => None
  | b :: T' => if passB b then match split_pass T' with Some (Pp, W) => Some (b :: Pp, W) | None => None end
               else Some ([], T)
  end.
Lemma split_pass_some T : forall Pp W, split_pass T = Some (Pp, W) -> T = Pp ++ W /\ forallb passB Pp = true.
Proof.
  induction T as [|b T IH]; intros Pp W H; cbn [split_pass] in H; [discriminate|].
  destruct (passB b) eqn:Eb.
  - destruct (split_pass T) as [[P1 W1]|] eqn:E; [|discriminate].
    sinj H. injection H as <- <-. destruct (IH P1 W1 eq_refl) as [-> HP].
    split; [reflexivity|]. cbn [forallb]. rewrite Eb, HP. reflexivity.
  - sinj H. injection H as <- <-. split; reflexivity.
Qed.
Lemma split_pass_none T : split_pass T = None -> forallb passB T = true.
Proof.
  induction T as [|b T IH]; intro H; cbn [split_pass] in H; [reflexivity|].
  destruct (passB b) eqn:Eb; [|discriminate].
  destruct (split_pass T) as [[P1 W1]|]; [discriminate|]. cbn [forallb]. rewrite Eb, (IH eq_refl). reflexivity.
Qed.

Inductive sres : Type := SOk (T B : list blk) | SHalt.
Definition scan (Tv : list blk) (deep : bool) (B : list blk) : option sres :=
  match split_pass Tv with
  | Some (Tp, W) =>
      if deep then None else
      match window (W ++ B) with
      | Some W' => Some (SOk Tp (canon W'))
      | None => if halt_pat (W ++ B) then Some SHalt else None
      end
  | None =>
      match split_pass B with
      | Some (Bp, W) =>
          match window W with
          | Some W' => Some (SOk Tv (canon (Bp ++ W')))
          | None => if halt_pat W then Some SHalt else None
          end
      | None => None
      end
  end.
Lemma scan_ok Tv deep B D T' B' : scan Tv deep B = Some (SOk T' B') -> (deep = false -> D = []) ->
  Scan (flat Tv ++ passive_items D ++ flat B) (flat T' ++ passive_items D ++ flat B').
Proof.
  intros H Hd. unfold scan in H.
  destruct (split_pass Tv) as [[Tp W]|] eqn:ET.
  - destruct (split_pass_some Tv Tp W ET) as [-> HP]. destruct deep; [discriminate|].
    rewrite (Hd eq_refl). cbn [passive_items app].
    destruct (window (W ++ B)) as [W'|] eqn:EW; [|destruct (halt_pat (W ++ B)); discriminate].
    sinj H. injection H as <- <-. rewrite canon_flat, !flat_app, (passB_flat Tp HP), <- app_assoc.
    apply scan_prefix. rewrite <- flat_app. exact (window_ok _ _ EW).
  - pose proof (split_pass_none Tv ET) as HT.
    destruct (split_pass B) as [[Bp W]|] eqn:EB; [|discriminate].
    destruct (split_pass_some B Bp W EB) as [-> HB].
    destruct (window W) as [W'|] eqn:EW; [|destruct (halt_pat W); discriminate].
    sinj H. injection H as <- <-. rewrite canon_flat, !flat_app, (passB_flat Tv HT), (passB_flat Bp HB).
    assert (E1 : forall X, passive_items (pm Tv) ++ passive_items D ++ (passive_items (pm Bp) ++ X) =
                           passive_items (pm Tv ++ D ++ pm Bp) ++ X)
      by (intro X; rewrite !passive_items_app, !app_assoc; reflexivity).
    rewrite !E1. apply scan_prefix. exact (window_ok W W' EW).
Qed.
Lemma scan_halt Tv deep B D : scan Tv deep B = Some SHalt -> (deep = false -> D = []) ->
  exists P, flat Tv ++ passive_items D ++ flat B = passive_items P ++ [(23%nat,true);(4%nat,false);(4%nat,true)].
Proof.
  intros H Hd. unfold scan in H.
  destruct (split_pass Tv) as [[Tp W]|] eqn:ET.
  - destruct (split_pass_some Tv Tp W ET) as [-> HP]. destruct deep; [discriminate|].
    rewrite (Hd eq_refl). cbn [passive_items app].
    destruct (window (W ++ B)); [discriminate|]. destruct (halt_pat (W ++ B)) eqn:EH; [|discriminate].
    exists (pm Tp). rewrite <- (halt_pat_spec _ EH), !flat_app, (passB_flat Tp HP), app_assoc. reflexivity.
  - pose proof (split_pass_none Tv ET) as HT.
    destruct (split_pass B) as [[Bp W]|] eqn:EB; [|discriminate].
    destruct (split_pass_some B Bp W EB) as [-> HB].
    destruct (window W); [discriminate|]. destruct (halt_pat W) eqn:EH; [|discriminate].
    exists (pm Tv ++ D ++ pm Bp). rewrite <- (halt_pat_spec _ EH), flat_app, (passB_flat Tv HT), (passB_flat Bp HB).
    rewrite !passive_items_app, !app_assoc. reflexivity.
Qed.

(* The state: counter, explicit top, deep FIFO of passive items, boundary blocks.
   A deep entry (m0,t0) stands for the item 5+2(m0+4(G-t0)): one fast-forward adds 8 to every
   deep item by incrementing the epoch G. *)
Record st : Type := mkst { cx : itN; tT : list blk; dF : list (N * N); dR : list (N * N);
                           dlen : N; dG : N; bB : list blk }.
Definition dm (G : N) (e : N * N) : nat := N.to_nat (fst e + 4 * (G - snd e)).
Definition dlist (s : st) : list (N * N) := dF s ++ rev (dR s).
Definition deep_items (s : st) : list item := passive_items (map (dm (dG s)) (dlist s)).
Definition interp (s : st) : list item := toI (cx s) :: flat (tT s) ++ deep_items s ++ flat (bB s).
Definition Inv (s : st) : Prop := N.to_nat (dlen s) = length (dlist s) /\ Forall (fun e => snd e <= dG s) (dlist s).
Definition Valid (s : st) : Prop := (c0 -->* record (interp s)) /\ Inv s.
Definition RP (r : st + bool) : Prop := match r with inl s' => Valid s' | inr b => b = true -> halts tm c0 end.
Definition StepOK (f : st -> option (st + bool)) : Prop := forall s r, f s = Some r -> Valid s -> RP r.

Lemma P_next s s' : Valid s -> Next (interp s) (interp s') -> Inv s' -> Valid s'.
Proof.
  intros [H1 _] HN HI. split; [|exact HI].
  eapply evstep_trans; [exact H1|]. apply progress_evstep. apply Next_sound. exact HN.
Qed.
Lemma P_id s s' : Valid s -> interp s' = interp s -> Inv s' -> Valid s'.
Proof. intros [H1 _] HE HI. split; [|exact HI]. rewrite HE. exact H1. Qed.
Definition with_top (s : st) (c : itN) (T B : list blk) : st := mkst c T (dF s) (dR s) (dlen s) (dG s) B.
Lemma interp_with_top s c T B : interp (with_top s c T B) = toI c :: flat T ++ deep_items s ++ flat B.
Proof. reflexivity. Qed.
Definition has_deep (s : st) : bool := match dF s, dR s with [], [] => false | _, _ => true end.
Lemma has_deep_false s : has_deep s = false -> map (dm (dG s)) (dlist s) = [].
Proof. unfold has_deep, dlist. destruct (dF s), (dR s); intro H; try discriminate. reflexivity. Qed.

(* the counter rules on binary items *)
Lemma Next_conv xs ys xs' ys' : Next xs ys -> xs = xs' -> ys = ys' -> Next xs' ys'.
Proof. intros H <- <-. exact H. Qed.
Lemma Nx_bar x h T : N.even x = true -> (x =? 0) = false -> head1N h = true ->
  Next (toI (x,true) :: toI h :: T) (toI (x-1,false) :: toI (3 + fst h, snd h) :: T).
Proof.
  intros Hx H0 Hh. bfacts. apply N.eqb_neq in H0. even Hx a.
  eapply Next_conv; [apply (next_bar (N.to_nat a - 1) _ T Hh)|leq|leq].
Qed.
Lemma Nx_zero_bar h T : head1N h = true ->
  Next (toI (0,true) :: toI h :: T) (toI (0,false) :: toI (0,false) :: toI (1 + fst h, snd h) :: T).
Proof. intros Hh. bfacts. eapply Next_conv; [apply (next_zero_bar _ T Hh)|leq|leq]. Qed.
Lemma Nx_comma x h T : N.even x = true -> (0 <? fst h) = true ->
  Next (toI (x,false) :: toI h :: T) (toI (x+2,true) :: toI h :: T).
Proof.
  intros Hx Hh. apply N.ltb_lt in Hh. even Hx a.
  assert (Hh' : (0 < fst (toI h))%nat) by (unfold toI; cbn [fst]; lia).
  eapply Next_conv; [apply (next_comma (N.to_nat a) _ T Hh')|leq|leq].
Qed.
Lemma Nx_merge x h T : N.even x = true ->
  Next (toI (x,false) :: toI (0,false) :: toI h :: T) (toI (3 + x + fst h, snd h) :: T).
Proof. intros Hx. even Hx a. eapply Next_conv; [apply (next_merge (N.to_nat a) (toI h) T)|leq|leq]. Qed.
Lemma Nx_odd x xs ys : N.odd x = true -> (3 <=? x) = true -> Scan xs ys ->
  Next (toI (x,false) :: xs) (toI (x-2,false) :: ys).
Proof. intros Hx H3 HS. bfacts. odd Hx a. eapply Next_conv; [apply (next_odd (N.to_nat a - 1) xs ys HS)|leq|leq]. Qed.
Lemma Nx_one e s0 T ys : (2 <=? e) = true -> Scan (toI (e-2, s0) :: T) ys ->
  Next (toI (1,false) :: toI (e,s0) :: T) (toI (0,false) :: toI (0,false) :: ys).
Proof.
  intros H2 HS. bfacts.
  assert (E : toI (e-2, s0) = ((N.to_nat e - 2)%nat, s0)) by (unfold toI; cbn [fst snd]; f_equal; lia).
  rewrite E in HS. eapply Next_conv; [apply (next_one (N.to_nat e - 2) s0 T ys HS)|leq|leq].
Qed.

(** ** The steps *)

Definition step_bar (s : st) : option (st + bool) :=
  match cx s, tT s with
  | (x, true), It h :: T' =>
      if N.even x && head1N h then
        if x =? 0 then Some (inl (with_top s (0,false) (It (0,false) :: It (1 + fst h, snd h) :: T') (bB s)))
        else Some (inl (with_top s (x-1,false) (It (3 + fst h, snd h) :: T') (bB s)))
      else None
  | _, _ => None
  end.
Lemma step_bar_ok : StepOK step_bar.
Proof.
  intros s r H HP. unfold step_bar in H. destruct s as [c T F R L G B]. cbn [cx tT bB] in H.
  dsimpl H; sinj H; bsplit; cbn [RP]; (eapply P_next; [exact HP| |exact (proj2 HP)]);
  rewrite interp_with_top; unfold interp; cbn [cx tT bB flat flat1 app].
  - match goal with Hz : (?z =? 0) = true |- _ => apply N.eqb_eq in Hz; subst z end. apply Nx_zero_bar; assumption.
  - apply Nx_bar; assumption.
Qed.

Definition step_even (s : st) : option (st + bool) :=
  match cx s with
  | (x, false) =>
      if N.even x then
        match tT s with
        | It (z, zs) :: T1 =>
            if (z =? 0) && negb zs then
              match T1 with It h :: T' => Some (inl (with_top s (3 + x + fst h, snd h) T' (bB s))) | _ => None end
            else if 0 <? z then Some (inl (with_top s (x+2, true) (tT s) (bB s))) else None
        | _ => None
        end
      else None
  | _ => None
  end.
Lemma step_even_ok : StepOK step_even.
Proof.
  intros s r H HP. unfold step_even in H. destruct s as [c T F R L G B]. cbn [cx tT bB] in H.
  dsimpl H; sinj H; bsplit; cbn [RP]; (eapply P_next; [exact HP| |exact (proj2 HP)]);
  rewrite interp_with_top; unfold interp; cbn [cx tT bB flat flat1 app].
  - match goal with Hz : (?z =? 0) = true |- _ => apply N.eqb_eq in Hz; subst z end.
    match goal with Hs : negb ?zs = true |- _ => destruct zs; [discriminate|] end. apply Nx_merge; assumption.
  - apply Nx_comma; assumption.
Qed.

Definition step_reset (s : st) : option (st + bool) :=
  match cx s, tT s with
  | (x, false), It (e, es) :: T' =>
      if (x =? 1) && (2 <=? e) then
        match scan (It (e-2, es) :: T') (has_deep s) (bB s) with
        | Some (SOk T'' B'') => Some (inl (with_top s (0,false) (It (0,false) :: T'') B''))
        | _ => None
        end
      else None
  | _, _ => None
  end.
Lemma step_reset_ok : StepOK step_reset.
Proof.
  intros s r H HP. unfold step_reset in H.
  destruct (cx s) as [x [|]] eqn:Ec; [discriminate|].
  destruct (tT s) as [|[[e es]|c] T'] eqn:ET; try discriminate.
  destruct ((x =? 1) && (2 <=? e)) eqn:C; [|discriminate]. bsplit. apply N.eqb_eq in H0. subst x.
  destruct (scan (It (e-2, es) :: T') (has_deep s) (bB s)) as [[T'' B''|]|] eqn:ES; try discriminate.
  sinj H. cbn [RP]. eapply P_next; [exact HP| |exact (proj2 HP)].
  rewrite interp_with_top. unfold interp. rewrite Ec, ET. cbn [flat flat1 app].
  apply Nx_one; [assumption|].
  pose proof (scan_ok _ _ _ (map (dm (dG s)) (dlist s)) _ _ ES (has_deep_false s)) as K.
  cbn [flat flat1 app] in K. exact K.
Qed.

Definition step_odd (s : st) : option (st + bool) :=
  match cx s with
  | (x, false) =>
      if N.odd x && (3 <=? x) then
        match scan (tT s) (has_deep s) (bB s) with
        | Some (SOk T'' B'') => Some (inl (with_top s (x-2,false) T'' B''))
        | Some SHalt => Some (inr true)
        | None => None
        end
      else None
  | _ => None
  end.
Lemma step_odd_ok : StepOK step_odd.
Proof.
  intros s r H HP. unfold step_odd in H.
  destruct (cx s) as [x [|]] eqn:Ec; [discriminate|].
  destruct (N.odd x && (3 <=? x)) eqn:C; [|discriminate]. bsplit.
  destruct (scan (tT s) (has_deep s) (bB s)) as [[T'' B''|]|] eqn:ES; try discriminate.
  - sinj H. cbn [RP]. eapply P_next; [exact HP| |exact (proj2 HP)].
    rewrite interp_with_top. unfold interp at 1. rewrite Ec.
    apply Nx_odd; [assumption|assumption|exact (scan_ok _ _ _ _ _ _ ES (has_deep_false s))].
  - sinj H. cbn [RP]. intros _.
    destruct (scan_halt _ _ _ _ ES (has_deep_false s)) as [P HPl].
    eapply halts_evstep; [|exact (proj1 HP)].
    unfold interp, deep_items. rewrite Ec, HPl. odd H0 a. apply N.leb_le in H1.
    replace (toI (2*a+1, false)) with (((3 + 2 * (N.to_nat a - 1))%nat, false))
      by (unfold toI; cbn [fst snd]; f_equal; lia).
    apply halt_window.
Qed.

(* the fast-forward: cross the front, all deep items, and the passive B items the counter can pay for *)
Fixpoint take_pass (budget : N) (B : list blk) : list itN * list blk :=
  match B with
  | It i :: B' =>
      if (0 <? budget) && passN i then let (c, r) := take_pass (budget - 1) B' in (i :: c, r) else ([], B)
  | _ => ([], B)
  end.
Lemma take_pass_spec budget B : forall c r, take_pass budget B = (c, r) -> B = map It c ++ r.
Proof.
  revert budget. induction B as [|b B IH]; intros budget c r H; cbn [take_pass] in H.
  - injection H as <- <-. reflexivity.
  - destruct b as [i|cc]; [|injection H as <- <-; reflexivity].
    destruct ((0 <? budget) && passN i); [|injection H as <- <-; reflexivity].
    destruct (take_pass (budget - 1) B) as [c1 r1] eqn:E. injection H as <- <-.
    rewrite (IH _ _ _ E). reflexivity.
Qed.
(* land on the next item if it starts with 1, else on the last crossed item *)
Definition ff_land (c : list itN) (r : list blk) : option (list itN * itN * list blk) :=
  match (match peek r with Some (h, r') => if head1N h then Some (h, r') else None | None => None end) with
  | Some (h, r') => Some (c, h, r')
  | None => match rev c with last :: rc => if head1N last then Some (rev rc, last, r) else None | [] => None end
  end.
Lemma ff_land_spec c r c' h r' : ff_land c r = Some (c', h, r') ->
  map toI c ++ flat r = map toI c' ++ toI h :: flat r' /\ head1N h = true.
Proof.
  unfold ff_land. intro H.
  assert (Back : forall l rc, rev c = l :: rc -> head1N l = true -> Some (rev rc, l, r) = Some (c', h, r') ->
            map toI c ++ flat r = map toI c' ++ toI h :: flat r' /\ head1N h = true).
  { intros l rc Er El E. sinj E. injection E as <- <- <-. split; [|exact El].
    rewrite <- (rev_involutive c), Er. cbn [rev]. rewrite map_app, <- app_assoc. reflexivity. }
  destruct (peek r) as [[h0 r0]|] eqn:E; [destruct (head1N h0) eqn:Eh|].
  - sinj H. injection H as <- <- <-. rewrite (peek_spec r h0 r0 E). split; [reflexivity|exact Eh].
  - destruct (rev c) as [|l rc] eqn:Er; [discriminate|]. destruct (head1N l) eqn:El; [|discriminate]. exact (Back l rc eq_refl El H).
  - destruct (rev c) as [|l rc] eqn:Er; [discriminate|]. destruct (head1N l) eqn:El; [|discriminate]. exact (Back l rc eq_refl El H).
Qed.
Definition conv1 (G : N) (i : itN) : N * N := (N.div2 (fst i - 5) + 4, G).
Definition step_ff (s : st) : option (st + bool) :=
  match cx s, tT s with
  | (x, false), [It (v, false)] =>
      if N.odd x && N.even v && (4 * (1 + dlen s) + 1 <=? x) then
        let (c, r) := take_pass ((x - 1) / 4 - 1 - dlen s) (bB s) in
        match ff_land c r with
        | Some (c', h, r') =>
            let k := N.of_nat (length c') in
            if forallb passN c' && (4 * (1 + dlen s + k) + 1 <=? x) then
              Some (inl (mkst (x - 4 * (1 + dlen s + k), false) [It (v + 5, false)]
                              (dF s) (rev (map (conv1 (dG s + 1)) c') ++ dR s)
                              (dlen s + k) (dG s + 1) (It (3 + fst h, snd h) :: r')))
            else None
        | None => None
        end
      else None
  | _, _ => None
  end.
Lemma map_toI_pass c : forallb passN c = true -> map toI c = passive_items (map mN c).
Proof.
  induction c as [|i c IH]; cbn [forallb map passive_items]; intro H; [reflexivity|].
  apply andb_prop in H as [Hi Hc]. rewrite (passN_toI i Hi), (IH Hc). reflexivity.
Qed.
Lemma dm_succ G e : snd e <= G -> dm (G + 1) e = (4 + dm G e)%nat.
Proof. intro H. unfold dm. lia. Qed.
Lemma dm_conv G i : dm G (conv1 G i) = (4 + mN i)%nat.
Proof. unfold dm, conv1, mN. cbn [fst snd]. rewrite N.sub_diag. lia. Qed.
Lemma progress_conv c1 c2 c1' c2' : c1 -->+ c2 -> c1 = c1' -> c2 = c2' -> c1' -->+ c2'.
Proof. intros H <- <-. exact H. Qed.
Lemma flat_map_It c : flat (map It c) = map toI c.
Proof. induction c as [|i c IH]; cbn [flat map flat1 app]; congruence. Qed.

Lemma step_ff_ok : StepOK step_ff.
Proof.
  intros s res H HP. unfold step_ff in H.
  destruct s as [cc T F R L G B]. cbn [cx tT dF dR dlen dG bB] in H.
  destruct cc as [x [|]]; [discriminate|].
  destruct T as [|[[v [|]]|cr] [|]]; try discriminate.
  destruct (N.odd x && N.even v && (4 * (1 + L) + 1 <=? x)) eqn:C1; [|discriminate].
  destruct (take_pass ((x - 1) / 4 - 1 - L) B) as [c r] eqn:ET.
  destruct (ff_land c r) as [[[c' h] r']|] eqn:EL; [|discriminate].
  destruct (forallb passN c' && (4 * (1 + L + N.of_nat (length c')) + 1 <=? x)) eqn:C2; [|discriminate].
  sinj H. cbn [RP].
  apply andb_prop in C1 as [C1 Hfuel]. apply andb_prop in C1 as [Hxo Hve].
  apply andb_prop in C2 as [Hc' Hfuel2]. apply N.leb_le in Hfuel2.
  destruct HP as [Hreach [HL HF]]. unfold dlist in HL, HF. cbn [dF dR dlen dG] in HL, HF.
  pose proof (take_pass_spec _ _ _ _ ET) as HB.
  destruct (ff_land_spec c r c' h r' EL) as [Hfl Hh].
  odd Hxo a. even Hve w.
  set (D := map (dm G) (F ++ rev R)). set (q := D ++ map mN c').
  assert (Hlen : length q = (N.to_nat L + length c')%nat).
  { unfold q, D. rewrite length_app, !length_map, HL. reflexivity. }
  assert (Hq : passive_items D ++ flat B = passive_items q ++ toI h :: flat r').
  { rewrite HB, flat_app. unfold q. rewrite passive_items_app, <- app_assoc. f_equal.
    rewrite flat_map_It, Hfl, (map_toI_pass c' Hc'). reflexivity. }
  split.
  - eapply evstep_trans; [exact Hreach|]. apply progress_evstep.
    unfold interp, deep_items, dlist. cbn [cx tT dF dR dG bB flat flat1 app].
    change (passive_items (map (dm G) (F ++ rev R))) with (passive_items D). rewrite Hq.
    pose proof (FF q [] (N.to_nat w) (toI h) (flat r') (N.to_nat a - 2 * (1 + length q))%nat (head1N_spec h Hh)) as K.
    cbn [passive_items app] in K.
    eapply progress_conv; [exact K| |].
    + f_equal. f_equal; [unfold toI; cbn [fst snd]; f_equal; lia|]. f_equal. unfold toI; cbn [fst snd]; f_equal; lia.
    + f_equal. f_equal; [unfold toI; cbn [fst snd]; f_equal; lia|].
      f_equal; [unfold toI; cbn [fst snd]; f_equal; lia|].
      rewrite rev_app_distr, rev_involutive, app_assoc, map_app, passive_items_app.
      unfold q. rewrite map_app, passive_items_app, <- !app_assoc. f_equal.
      * f_equal. unfold D. rewrite map_map. apply map_ext_in. intros e He.
        rewrite Forall_forall in HF. rewrite (dm_succ G e (HF e He)). reflexivity.
      * f_equal.
        -- f_equal. rewrite !map_map. apply map_ext. intro i. rewrite dm_conv. reflexivity.
        -- f_equal. rewrite toI_add. reflexivity.
  - unfold Inv, dlist. cbn [dF dR dlen dG]. split.
    + rewrite rev_app_distr, rev_involutive, app_assoc, length_app, <- HL, length_map. lia.
    + rewrite rev_app_distr, rev_involutive, app_assoc. apply Forall_app. split.
      * eapply Forall_impl; [|exact HF]. intros e He. cbn beta in He. lia.
      * apply Forall_forall. intros e He. apply in_map_iff in He as [i [<- _]]. unfold conv1. cbn [snd]. lia.
Qed.

(* identities: hand the last deep item back to B, or pull the next item up into the top *)
Definition pval (G : N) (e : N * N) : N := 5 + 2 * (fst e + 4 * (G - snd e)).
Lemma toI_pval G e : toI (pval G e, false) = ((5 + 2 * dm G e)%nat, false).
Proof. unfold toI, pval, dm. cbn [fst snd]. f_equal. lia. Qed.
Definition pop_back (F R : list (N * N)) : option ((N * N) * list (N * N) * list (N * N)) :=
  match R with e :: R' => Some (e, F, R') | [] => match rev F with e :: rF => Some (e, [], rF) | [] => None end end.
Lemma pop_back_spec F R e F' R' : pop_back F R = Some (e, F', R') -> F ++ rev R = (F' ++ rev R') ++ [e].
Proof.
  unfold pop_back. intro H. destruct R as [|e0 R0].
  - destruct (rev F) as [|e1 rF] eqn:E; [discriminate|]. sinj H. injection H as <- <- <-.
    rewrite <- (rev_involutive F), E. cbn [rev app]. rewrite !app_nil_r. reflexivity.
  - sinj H. injection H as <- <- <-. cbn [rev]. rewrite app_assoc. reflexivity.
Qed.
Definition pop_front (F R : list (N * N)) : option ((N * N) * list (N * N) * list (N * N)) :=
  match F with e :: F' => Some (e, F', R) | [] => match rev R with e :: rR => Some (e, rR, []) | [] => None end end.
Lemma pop_front_spec F R e F' R' : pop_front F R = Some (e, F', R') -> F ++ rev R = e :: (F' ++ rev R').
Proof.
  unfold pop_front. intro H. destruct F as [|e0 F0].
  - destruct (rev R) as [|e1 rR] eqn:E; [discriminate|]. sinj H. injection H as <- <- <-.
    cbn [app rev]. rewrite app_nil_r. reflexivity.
  - sinj H. injection H as <- <- <-. reflexivity.
Qed.
Lemma pop_front_none F R : pop_front F R = None -> F ++ rev R = [].
Proof. unfold pop_front. destruct F; [|discriminate]. destruct (rev R) eqn:E; [|discriminate]. reflexivity. Qed.

Definition step_unmig (s : st) : option (st + bool) :=
  match cx s, tT s with
  | (x, false), [It (v, false)] =>
      if N.odd x && (5 <=? x) && N.even v then
        match pop_back (dF s) (dR s) with
        | Some (e, F', R') => Some (inl (mkst (cx s) (tT s) F' R' (dlen s - 1) (dG s) (It (pval (dG s) e, false) :: bB s)))
        | None => None
        end
      else None
  | _, _ => None
  end.
Lemma step_unmig_ok : StepOK step_unmig.
Proof.
  intros s res H HP. unfold step_unmig in H.
  destruct s as [c T F R L G B]. cbn [cx tT dF dR dlen dG bB] in H.
  destruct c as [x [|]]; [discriminate|].
  destruct T as [|[[v [|]]|cr] [|]]; try discriminate.
  destruct (N.odd x && (5 <=? x) && N.even v); [|discriminate].
  destruct (pop_back F R) as [[[e F'] R']|] eqn:EP; [|discriminate].
  sinj H. cbn [RP]. apply pop_back_spec in EP.
  destruct HP as [Hreach [HL HF]]. unfold dlist in HL, HF. cbn [dF dR dlen dG] in HL, HF. rewrite EP in HL, HF.
  eapply P_id; [split; [exact Hreach|split; unfold dlist; cbn [dF dR dlen dG]; rewrite EP; assumption]| |].
  - unfold interp, deep_items, dlist. cbn [cx tT dF dR dG bB flat flat1 app].
    rewrite EP, !map_app, !passive_items_app, <- !app_assoc. cbn [map passive_items app]. rewrite toI_pval. reflexivity.
  - unfold Inv, dlist. cbn [dF dR dlen dG]. split.
    + rewrite length_app in HL. cbn [length] in HL. lia.
    + apply Forall_app in HF. exact (proj1 HF).
Qed.

Definition step_pull (s : st) : option (st + bool) :=
  match pop_front (dF s) (dR s) with
  | Some (e, F', R') => Some (inl (mkst (cx s) (tT s ++ [It (pval (dG s) e, false)]) F' R' (dlen s - 1) (dG s) (bB s)))
  | None =>
      match peek (bB s) with
      | Some (i, B') => Some (inl (mkst (cx s) (tT s ++ [It i]) (dF s) (dR s) (dlen s) (dG s) B'))
      | None => None
      end
  end.
Lemma step_pull_ok : StepOK step_pull.
Proof.
  intros s res H HP. unfold step_pull in H.
  destruct s as [c T F R L G B]. cbn [cx tT dF dR dlen dG bB] in H.
  destruct HP as [Hreach [HL HF]]. unfold dlist in HL, HF. cbn [dF dR dlen dG] in HL, HF.
  destruct (pop_front F R) as [[[e F'] R']|] eqn:EP.
  - sinj H. cbn [RP]. apply pop_front_spec in EP. rewrite EP in HL, HF.
    eapply P_id; [split; [exact Hreach|split; unfold dlist; cbn [dF dR dlen dG]; rewrite EP; assumption]| |].
    + unfold interp, deep_items, dlist. cbn [cx tT dF dR dG bB].
      rewrite EP, flat_app. cbn [flat flat1 app map passive_items]. rewrite toI_pval, <- app_assoc. reflexivity.
    + unfold Inv, dlist. cbn [dF dR dlen dG]. split; [cbn [length] in HL; lia|inversion HF; assumption].
  - destruct (peek B) as [[i B']|] eqn:EB; [|discriminate].
    sinj H. cbn [RP]. pose proof (pop_front_none F R EP) as E0.
    eapply P_id; [split; [exact Hreach|split; assumption]| |].
    + unfold interp, deep_items, dlist. cbn [cx tT dF dR dG bB].
      rewrite E0, (peek_spec B i B' EB), flat_app, <- app_assoc. cbn [flat flat1 app map passive_items]. reflexivity.
    + split; assumption.
Qed.

(** ** The run *)

Definition steps : list (st -> option (st + bool)) :=
  [step_bar; step_even; step_reset; step_ff; step_unmig; step_odd; step_pull].
Definition tick (s : st) : st + bool := match first_some steps s with Some r => r | None => inr false end.
Lemma tick_ok s : Valid s -> RP (tick s).
Proof.
  intro HP. unfold tick. destruct (first_some steps s) as [r|] eqn:E; [|cbn [RP]; discriminate].
  pose proof (first_some_spec (fun s r => Valid s -> RP r) steps s r) as K. cbn beta in K.
  apply K; [|exact E|exact HP].
  repeat constructor;
  [ exact step_bar_ok | exact step_even_ok | exact step_reset_ok | exact step_ff_ok
  | exact step_unmig_ok | exact step_odd_ok | exact step_pull_ok ].
Qed.

Definition init_st : st := mkst (0, false) [It (0, false); It (3, false)] [] [] 0 0 [It (4, true)].
Definition check (fuel : N) : bool :=
  match N_iter_until tick (inl init_st) fuel with inr true => true | _ => false end.

Theorem check_spec fuel : check fuel = true -> halts tm c0.
Proof.
  unfold check. intro H.
  assert (I : Valid init_st) by (split; [exact init|split; [reflexivity|constructor]]).
  pose proof (N_iter_until_spec (f := tick) (x := inl init_st) (T := fuel)
                Valid (fun b => b = true -> halts tm c0) tick_ok I) as K.
  destruct (N_iter_until tick (inl init_st) fuel) as [s|[|]]; [discriminate|exact (K eq_refl)|discriminate].
Qed.

Ltac native_check_eq := match goal with |- _ = ?a => native_cast_no_check (eq_refl a) end.

(* 1307718 ticks; about 2.5 minutes where native_compute falls back to vm_compute *)
Theorem halt : halts tm c0.
Proof. apply (check_spec 3000000). native_check_eq. Qed.

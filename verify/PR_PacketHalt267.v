(* Halting of BB(6) holdout #267 (1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RA---).
   METHOD AND MOST TEXT: valu42's PacketHalt274.v (valu42/busycoqtesting, branch prove-halt-274). His, copied with
   small changes: the longitudinal packet frame (head stream C/[0] -> A/[0]), the outcome semantics Sem with
   sem_input_eq / sem_segment / calls_addN / sem_after / sem_early / packet_return / sem_single / sem_child, the fuel
   evaluator's shape, the boundary seed and the checked orbit.
   New here: the packets are not hand-picked. Each packet law is checked by computation with busycoq's
   BoundedConfig.segRLs_c (soundness: BoundedConfig.segRLs_c_spec); a batch is any fixed-length law cycle (pre-period
   + period, via Longitudinal.segRLs_addmul_v2); decode walks a trie of the short packets (<= 14 cells: a batch first,
   else the first packet) and falls back to the shortest matching long packet. The table was found by simulation.
   This proves the outcome only, not the running time. *)
From BusyCoq Require Import Individual62 Longitudinal LongitudinalHalt.
From Coq Require Import String List Lia Arith NArith Bool.
Import ListNotations.
Open Scope list.
Set Warnings "-abstract-large-number".

Module TM1.
Definition tm := Eval compute in
  TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RA---".
Definition hR : DH0 := (C,[0]).
Definition hL : DH0 := (A,[0]).
Definition h := [(hR,hL)].
Definition Calls (n:N) := h^^N.to_nat n.

(* ---------------- packet laws checked by computation (Kestrel) ---------------- *)
Definition LT : nat := (348002)%nat.
Definition law_ok (u v:list Sym) (k:nat) : bool := BoundedConfig.segRLs_c tm h (h^^k) u v LT.
Lemma law_ok_sound u v k : law_ok u v k = true -> segRLs tm h (h^^k) u v.
Proof. intros H. eapply BoundedConfig.segRLs_c_spec. exact H. Qed.
(* tactics must never unfold the checker inside proofs (vm_compute ignores this) *)
Global Opaque law_ok LT.

Definition sym_eqb (a b:Sym) : bool :=
 match a, b with S0, S0 => true | S1, S1 => true | _, _ => false end.
Fixpoint lsym_eqb (u v:list Sym) : bool :=
 match u, v with
 | [], [] => true
 | a::u', b::v' => sym_eqb a b && lsym_eqb u' v'
 | _, _ => false
 end.
Lemma lsym_eqb_eq u v : lsym_eqb u v = true -> u = v.
Proof.
 revert v. induction u as [|a u IH]; intros [|b v] H; cbn in H; try discriminate; [reflexivity|].
 apply andb_prop in H as [H1 H2]. destruct a, b; cbn in H1; try discriminate; f_equal; apply IH, H2.
Qed.

(* a chain of laws: (w_i,k_i) :: ... means w_i -> (next word) with k_i calls out; the last one goes to [back] *)
Definition start_of (l:list (list Sym * nat)) (back:list Sym) : list Sym :=
 match l with [] => back | (w,_)::_ => w end.
Fixpoint chain_ok (l:list (list Sym * nat)) (back:list Sym) : bool :=
 match l with
 | [] => true
 | (w,k)::l' => law_ok w (start_of l' back) k && chain_ok l' back
 end.
Fixpoint sumk (l:list (list Sym * nat)) : nat :=
 match l with [] => 0%nat | (_,k)::l' => k + sumk l' end.

Lemma lpow_h1 : h^^1%nat = h.
Proof. reflexivity. Qed.

Lemma chain_law l back : chain_ok l back = true -> forall j, j <= length l ->
 segRLs tm (h^^j) (h^^(sumk (firstn j l))) (start_of l back) (start_of (skipn j l) back).
Proof.
 induction l as [|[w k] l IH]; intros Hok j Hj.
 - cbn in Hj. assert (j = 0%nat) by lia. subst. cbn. constructor.
 - destruct j as [|j]; [cbn; constructor|].
   cbn in Hok. apply andb_prop in Hok as [H1 H2].
   cbn[firstn skipn sumk length] in *.
   replace (S j) with (1+j) by lia.
   eapply segRLs_trans_add.
   + rewrite lpow_h1. apply law_ok_sound. exact H1.
   + apply IH; [exact H2|lia].
Qed.

(* ---------------- table entries ---------------- *)
Inductive Entry :=
| EB (pre cyc:list (list Sym * nat))
| EO (u v:list Sym) (k:nat)
| EH (u:list Sym).

Definition cyc_start (cyc:list (list Sym * nat)) : list Sym := start_of cyc [].
Definition entry_u (e:Entry) : list Sym :=
 match e with EB pre cyc => start_of pre (cyc_start cyc) | EO u _ _ => u | EH u => u end.

Definition UH : list Sym := [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1].
Lemma UH_halts l r : halts tm (l {{{(hR,R)}}} UH *> r).
Proof. unfold hR, UH. solve_halt. Qed.

Definition entry_ok (e:Entry) : bool :=
 match e with
 | EB pre cyc =>
   match cyc with
   | [] => false
   | _ => chain_ok pre (cyc_start cyc) && chain_ok cyc (cyc_start cyc)
   end
 | EO u v k => law_ok u v k
 | EH u => lsym_eqb u UH
 end.

(* batches: n calls on a fixed-length law cycle, in binary arithmetic. The counts get thousands of bits long, so
   division by a power-of-two period is a shift and the remainder a mask (N.div / N.modulo are bit-serial in the VM),
   and products are written small * big. *)
Definition is_pow2 (p:N) : bool := N.eqb (2 ^ N.log2 p) p.
Definition qdiv (a p:N) : N := if is_pow2 p then N.shiftr a (N.log2 p) else (a / p)%N.
Definition qmod (a p:N) : N := if is_pow2 p then N.land a (N.ones (N.log2 p)) else (a mod p)%N.
Lemma qdiv_eq a p : qdiv a p = (a / p)%N.
Proof.
 unfold qdiv, is_pow2. destruct (N.eqb_spec (2 ^ N.log2 p) p) as [E|E]; [|reflexivity].
 rewrite N.shiftr_div_pow2, E. reflexivity.
Qed.
Lemma qmod_eq a p : qmod a p = (a mod p)%N.
Proof.
 unfold qmod, is_pow2. destruct (N.eqb_spec (2 ^ N.log2 p) p) as [E|E]; [|reflexivity].
 rewrite N.land_ones, E. reflexivity.
Qed.
Definition b_out (pre cyc:list (list Sym * nat)) (n:N) : N :=
 let c0 := N.of_nat (length pre) in
 let p := N.of_nat (length cyc) in
 if N.ltb n c0 then N.of_nat (sumk (firstn (N.to_nat n) pre))
 else N.of_nat (sumk pre) + N.of_nat (sumk cyc) * qdiv (n - c0) p + N.of_nat (sumk (firstn (N.to_nat (qmod (n - c0) p)) cyc)).
Definition b_word (pre cyc:list (list Sym * nat)) (n:N) : list Sym :=
 let c0 := N.of_nat (length pre) in
 let p := N.of_nat (length cyc) in
 if N.ltb n c0 then start_of (skipn (N.to_nat n) pre) (cyc_start cyc)
 else start_of (skipn (N.to_nat (qmod (n - c0) p)) cyc) (cyc_start cyc).

Lemma start_of_cons (c:list Sym * nat) l b b' : start_of (c::l) b = start_of (c::l) b'.
Proof. destruct c; reflexivity. Qed.

Lemma divmod_nat (n c0 p:N) : p <> 0%N -> (c0 <= n)%N ->
 N.to_nat n = N.to_nat ((n - c0) / p) * N.to_nat p + N.to_nat c0 + N.to_nat ((n - c0) mod p) /\
 N.to_nat ((n - c0) mod p) < N.to_nat p.
Proof.
 intros Hp Hc. pose proof (N.div_mod (n - c0) p Hp) as Hdm. pose proof (N.mod_lt (n - c0) p Hp) as Hr.
 split.
 - rewrite <- (N.sub_add c0 n Hc) at 1. rewrite Hdm at 1. rewrite !N2Nat.inj_add, N2Nat.inj_mul. ring.
 - lia.
Qed.

Lemma batch_law_aux pre cyc n : cyc <> [] ->
 chain_ok pre (cyc_start cyc) = true -> chain_ok cyc (cyc_start cyc) = true ->
 segRLs tm (Calls n) (Calls (b_out pre cyc n)) (start_of pre (cyc_start cyc)) (b_word pre cyc n).
Proof.
 intros Hne Hpre Hcyc.
 assert (Hs : start_of cyc (cyc_start cyc) = cyc_start cyc)
   by (destruct cyc as [|c l]; [contradiction|unfold cyc_start; apply start_of_cons]).
 assert (Hp : length cyc <> 0%nat) by (destruct cyc; [contradiction|cbn; lia]).
 unfold Calls, b_out, b_word. cbv zeta.
 destruct (N.ltb n (N.of_nat (length pre))) eqn:Elt.
 - apply N.ltb_lt in Elt. rewrite Nat2N.id.
   apply (chain_law pre (cyc_start cyc) Hpre (N.to_nat n)).
   lia.
 - apply N.ltb_ge in Elt.
   rewrite !qdiv_eq, !qmod_eq.
   assert (Hpn : N.of_nat (length cyc) <> 0%N).
   { intro E. apply Hp. apply (f_equal N.to_nat) in E. rewrite Nat2N.id in E. exact E. }
   destruct (divmod_nat n (N.of_nat (length pre)) (N.of_nat (length cyc)) Hpn Elt) as [Hn Hrn].
   repeat rewrite Nat2N.id in Hn. repeat rewrite Nat2N.id in Hrn.
   set (q := ((n - N.of_nat (length pre)) / N.of_nat (length cyc))%N) in *.
   set (r := ((n - N.of_nat (length pre)) mod N.of_nat (length cyc))%N) in *.
   apply Nat.lt_le_incl in Hrn.
   rewrite Hn.
   replace (N.to_nat (N.of_nat (sumk pre) + N.of_nat (sumk cyc) * q + N.of_nat (sumk (firstn (N.to_nat r) cyc))))
     with (N.to_nat q * sumk cyc + sumk pre + sumk (firstn (N.to_nat r) cyc))
     by (rewrite !N2Nat.inj_add, N2Nat.inj_mul, !Nat2N.id; ring).
   eapply segRLs_trans_add.
   + apply segRLs_addmul_v2.
     * pose proof (chain_law pre (cyc_start cyc) Hpre (length pre) (le_n _)) as H.
       rewrite firstn_all, skipn_all in H. exact H.
     * pose proof (chain_law cyc (cyc_start cyc) Hcyc (length cyc) (le_n _)) as H.
       rewrite firstn_all, skipn_all, Hs in H. exact H.
   + pose proof (chain_law cyc (cyc_start cyc) Hcyc (N.to_nat r) Hrn) as H.
     rewrite Hs in H. exact H.
Qed.

Lemma batch_law pre cyc : entry_ok (EB pre cyc) = true -> forall n,
 segRLs tm (Calls n) (Calls (b_out pre cyc n)) (entry_u (EB pre cyc)) (b_word pre cyc n).
Proof.
 intros Hok n.
 assert (Hne : cyc <> []) by (intro E; subst cyc; discriminate).
 assert (Hand : chain_ok pre (cyc_start cyc) && chain_ok cyc (cyc_start cyc) = true)
   by (destruct cyc; [contradiction|exact Hok]).
 apply andb_prop in Hand as [Hpre Hcyc].
 apply batch_law_aux; assumption.
Qed.

(* ---------------- decode: a trie of short packets, then the long ones ---------------- *)
Definition pop (w:list Sym) : Sym * list Sym :=
 match w with [] => (0,[]) | b::t => (b,t) end.
Lemma pop_sound w :
 w *> 0inf = [fst (pop w)] *> (snd (pop w) *> 0inf).
Proof.
 destruct w as [|b t]; cbn[pop fst snd Str_app].
 - apply const_unfold.
 - reflexivity.
Qed.

Fixpoint take_pad (m:nat) (w:list Sym) : list Sym * list Sym :=
 match m with
 | O => ([], w)
 | S m => let p := take_pad m (snd (pop w)) in (fst (pop w) :: fst p, snd p)
 end.
Lemma take_pad_sound m w : w *> 0inf = fst (take_pad m w) *> (snd (take_pad m w) *> 0inf).
Proof.
 revert w. induction m as [|m IH]; intros w; [reflexivity|].
 transitivity ([fst (pop w)] *> (snd (pop w) *> 0inf)); [apply pop_sound|].
 cbn [take_pad fst snd Str_app]. f_equal. exact (IH (snd (pop w))).
Qed.

Inductive Trie := TNil | TNode (e:option Entry) (t0 t1:Trie).
Definition child (b:Sym) (t0 t1:Trie) : Trie := match b with S0 => t0 | S1 => t1 end.
(* within 14 cells: the first batch packet wins; a halting packet wins if no packet came before it; else the
   first packet (the rule of mirror.py / geneval2.py) *)
Fixpoint walk (tr:Trie) (w:list Sym) (d:nat) (first:option Entry) {struct d} : option Entry :=
 match d with
 | O => first
 | S d =>
   match tr with
   | TNil => first
   | TNode _ t0 t1 =>
     match child (fst (pop w)) t0 t1 with
     | TNil => first
     | TNode e s0 s1 =>
       match e with
       | Some (EB pre cyc) => Some (EB pre cyc)
       | Some (EO u v k) =>
         match first with
         | None => walk (TNode e s0 s1) (snd (pop w)) d (Some (EO u v k))
         | Some _ => walk (TNode e s0 s1) (snd (pop w)) d first
         end
       | Some (EH u) =>
         match first with
         | None => Some (EH u)
         | Some _ => walk (TNode e s0 s1) (snd (pop w)) d first
         end
       | None => walk (TNode e s0 s1) (snd (pop w)) d first
       end
     end
   end
 end.
Fixpoint trie_all (f:Entry -> bool) (tr:Trie) : bool :=
 match tr with
 | TNil => true
 | TNode e t0 t1 => match e with Some x => f x | None => true end && trie_all f t0 && trie_all f t1
 end.
Lemma trie_all_child f b t0 t1 : trie_all f t0 = true -> trie_all f t1 = true -> trie_all f (child b t0 t1) = true.
Proof. destruct b; auto. Qed.
Lemma walk_ok f tr w d first e :
 trie_all f tr = true -> (forall x, first = Some x -> f x = true) -> walk tr w d first = Some e -> f e = true.
Proof.
 revert tr w first. induction d as [|d IH]; intros tr w first Ht Hf Hw.
 - cbn in Hw. apply Hf. exact Hw.
 - destruct tr as [|e0 t0 t1].
   + cbn in Hw. apply Hf. exact Hw.
   + cbn[trie_all] in Ht. apply andb_prop in Ht as [Ht Ht1]. apply andb_prop in Ht as [_ Ht0].
     pose proof (trie_all_child f (fst (pop w)) t0 t1 Ht0 Ht1) as Htr.
     cbn[walk] in Hw. revert Htr Hw.
     destruct (child (fst (pop w)) t0 t1) as [|e1 s0 s1]; intros Htr Hw.
     * apply Hf. exact Hw.
     * assert (He1 : forall x, e1 = Some x -> f x = true).
       { intros x Ex. subst e1. cbn[trie_all] in Htr. apply andb_prop in Htr as [Htr _].
         apply andb_prop in Htr as [Hx _]. exact Hx. }
       destruct e1 as [[pre cyc|u v k|u]|].
       -- cbn beta iota in Hw. injection Hw as <-. apply He1. reflexivity.
       -- destruct first as [y|]; cbn beta iota in Hw.
          ++ eapply IH; [exact Htr|exact Hf|exact Hw].
          ++ eapply IH; [exact Htr| |exact Hw]. intros z Ez. injection Ez as <-. apply He1. reflexivity.
       -- destruct first as [y|]; cbn beta iota in Hw.
          ++ eapply IH; [exact Htr|exact Hf|exact Hw].
          ++ injection Hw as <-. apply He1. reflexivity.
       -- cbn beta iota in Hw. eapply IH; [exact Htr|exact Hf|exact Hw].
Qed.

Fixpoint scan (l:list Entry) (w:list Sym) : option (Entry * list Sym) :=
 match l with
 | [] => None
 | e::l' =>
   let '(u,t) := take_pad (length (entry_u e)) w in
   if lsym_eqb u (entry_u e) then Some (e,t) else scan l' w
 end.
Lemma scan_ok l w e t : forallb entry_ok l = true -> scan l w = Some (e,t) ->
 entry_ok e = true /\ w *> 0inf = entry_u e *> (t *> 0inf).
Proof.
 induction l as [|e0 l IH]; intros Hl Hs; cbn[scan] in Hs; [discriminate|].
 cbn[forallb] in Hl. apply andb_prop in Hl as [H0 Hl].
 pose proof (take_pad_sound (length (entry_u e0)) w) as Hw.
 revert Hs Hw. destruct (take_pad (length (entry_u e0)) w) as [u t0]. cbn[fst snd]. intros Hs Hw.
 cbn beta iota in Hs.
 destruct (lsym_eqb u (entry_u e0)) eqn:Eq.
 - injection Hs as <- <-. apply lsym_eqb_eq in Eq. subst u. split; assumption.
 - apply IH; assumption.
Qed.

Definition E0 : Entry := EO [0] [1] 0%nat.
Definition E1 : Entry := EB [] [([0;0;0],0%nat); ([1;0;0],1%nat)].
Definition E2 : Entry := EB [] [([1;0;0],1%nat); ([0;0;0],0%nat)].
Definition E3 : Entry := EB [([0;0;1;0],0%nat)] [([1;0;1;0],2%nat)].
Definition E4 : Entry := EB [] [([1;0;1;0],2%nat)].
Definition E5 : Entry := EB [([0;0;1;1;0;0],0%nat); ([1;0;1;1;0;0],0%nat)] [([0;0;0;1;0;0],0%nat); ([1;0;0;1;0;0],1%nat); ([0;0;0;0;0;0],0%nat); ([1;0;0;0;0;0],0%nat)].
Definition E6 : Entry := EB [([0;1;0;1;0;0],0%nat); ([1;1;0;1;0;0],1%nat)] [([0;0;0;0;0;0],0%nat); ([1;0;0;0;0;0],0%nat); ([0;0;0;1;0;0],0%nat); ([1;0;0;1;0;0],1%nat)].
Definition E7 : Entry := EB [([1;0;1;1;0;0],0%nat)] [([0;0;0;1;0;0],0%nat); ([1;0;0;1;0;0],1%nat); ([0;0;0;0;0;0],0%nat); ([1;0;0;0;0;0],0%nat)].
Definition E8 : Entry := EB [([1;1;0;1;0;0],1%nat)] [([0;0;0;0;0;0],0%nat); ([1;0;0;0;0;0],0%nat); ([0;0;0;1;0;0],0%nat); ([1;0;0;1;0;0],1%nat)].
Definition E9 : Entry := EB [([0;0;1;1;0;1;0],0%nat); ([1;0;1;1;0;1;0],0%nat)] [([0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0],2%nat)].
Definition E10 : Entry := EB [([0;1;0;0;0;0;0],0%nat); ([1;1;0;0;0;0;0],2%nat)] [([0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0],2%nat)].
Definition E11 : Entry := EB [([0;1;0;1;0;1;0],0%nat); ([1;1;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0],2%nat)].
Definition E12 : Entry := EB [([1;0;1;1;0;1;0],0%nat)] [([0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0],2%nat)].
Definition E13 : Entry := EB [([1;1;0;0;0;0;0],2%nat)] [([0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0],2%nat)].
Definition E14 : Entry := EB [([1;1;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0],2%nat)].
Definition E15 : Entry := EB [([0;1;0;0;0;0;1;0;0],0%nat); ([1;1;0;0;0;0;1;0;0],0%nat)] [([0;0;0;0;0;0;1;0;0],0%nat); ([1;0;0;0;0;0;1;0;0],0%nat); ([0;0;0;1;0;0;1;0;0],0%nat); ([1;0;0;1;0;0;1;0;0],1%nat); ([0;0;0;0;0;0;0;0;0],0%nat); ([1;0;0;0;0;0;0;0;0],0%nat); ([0;0;0;1;0;0;0;0;0],0%nat); ([1;0;0;1;0;0;0;0;0],0%nat)].
Definition E16 : Entry := EB [([0;1;0;0;0;0;1;0;1;0],0%nat); ([1;1;0;0;0;0;1;0;1;0],0%nat)] [([0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E17 : Entry := EB [([0;1;0;0;1;0;0;0;0;0],0%nat); ([1;1;0;0;1;0;0;0;0;0],0%nat)] [([0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E18 : Entry := EB [([0;1;0;1;1;0;0;0;0;0],0%nat); ([1;1;0;1;1;0;0;0;0;0],2%nat)] [([0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E19 : Entry := EO [1;1;0;0;1;0;1;0;1;0;0] [0;0;0;0;0;0;1;0;0;0;0] 1%nat.
Definition E20 : Entry := EB [([0;1;0;0;1;0;0;0;0;1;0;0],0%nat); ([1;1;0;0;1;0;0;0;0;1;0;0],0%nat); ([0;0;0;0;0;0;1;0;1;1;0;0],0%nat); ([1;0;0;0;0;0;1;0;1;1;0;0],0%nat); ([0;0;0;1;0;0;1;0;1;1;0;0],0%nat); ([1;0;0;1;0;0;1;0;1;1;0;0],0%nat)] [([0;0;0;0;0;0;0;0;0;1;0;0],0%nat); ([1;0;0;0;0;0;0;0;0;1;0;0],0%nat); ([0;0;0;1;0;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;0;0;0;0;1;0;0],0%nat); ([0;0;0;0;0;0;1;0;0;1;0;0],0%nat); ([1;0;0;0;0;0;1;0;0;1;0;0],0%nat); ([0;0;0;1;0;0;1;0;0;1;0;0],0%nat); ([1;0;0;1;0;0;1;0;0;1;0;0],1%nat); ([0;0;0;0;0;0;0;0;0;0;0;0],0%nat); ([1;0;0;0;0;0;0;0;0;0;0;0],0%nat); ([0;0;0;1;0;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;0;0;0;0;0;0;0],0%nat); ([0;0;0;0;0;0;1;0;0;0;0;0],0%nat); ([1;0;0;0;0;0;1;0;0;0;0;0],0%nat); ([0;0;0;1;0;0;1;0;0;0;0;0],0%nat); ([1;0;0;1;0;0;1;0;0;0;0;0],0%nat)].
Definition E21 : Entry := EO [1;1;0;0;1;0;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0] 1%nat.
Definition E22 : Entry := EO [1;1;0;0;1;0;1;0;0;0;0;0] [0;0;0;0;0;0;1;0;1;0;1;0] 2%nat.
Definition E23 : Entry := EO [1;1;0;0;1;0;1;0;1;0;1;0] [0;0;0;0;0;0;1;0;1;0;1;0] 2%nat.
Definition E24 : Entry := EB [([0;1;0;0;1;0;1;0;0;0;0;1;0],0%nat); ([1;1;0;0;1;0;1;0;0;0;0;1;0],0%nat); ([0;0;0;0;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;0;0;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;0;0;0;1;0],0%nat)] [([0;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E25 : Entry := EB [([0;1;0;0;1;0;1;0;0;1;0;0;0],0%nat); ([1;1;0;0;1;0;1;0;0;1;0;0;0],1%nat); ([0;0;0;0;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;0;0;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;0;0;0;1;0],0%nat)] [([0;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E26 : Entry := EB [([0;1;0;0;1;0;1;0;1;0;0;0;0],0%nat); ([1;1;0;0;1;0;1;0;1;0;0;0;0],0%nat); ([0;0;0;0;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;0;0;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;0;0;0;1;0],0%nat)] [([0;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E27 : Entry := EB [([0;1;0;1;1;0;0;1;0;0;0;0;0],0%nat); ([1;1;0;1;1;0;0;1;0;0;0;0;0],0%nat)] [([0;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E28 : Entry := EB [([0;1;0;0;1;0;0;1;0;0;0;0;0;0],0%nat); ([1;1;0;0;1;0;0;1;0;0;0;0;0;0],0%nat)] [([0;0;0;1;0;1;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;1;0],2%nat)].
Definition E29 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;0;0;0] 1%nat.
Definition E30 : Entry := EO [1;1;0;1;1;0;0;1;0;0;1;0;0;0;0] [0;0;0;0;0;0;1;0;1;0;1;0;0;1;0] 1%nat.
Definition E31 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E32 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E33 : Entry := EB [([1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0],1%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0],0%nat)] [([0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E34 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0],1%nat)].
Definition E35 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E36 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1] 0%nat.
Definition E37 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E38 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0] 1%nat.
Definition E39 : Entry := EO [1;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0] [0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E40 : Entry := EB [([1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0],1%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;0;0;0],0%nat)] [([0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0],0%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0],1%nat)].
Definition E41 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0] 1%nat.
Definition E42 : Entry := EB [([1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;0],2%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;1;0;1;0],0%nat)] [([0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],4%nat)].
Definition E43 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;0;0;0;1] 0%nat.
Definition E44 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;0;0] 1%nat.
Definition E45 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0] 2%nat.
Definition E46 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0] 2%nat.
Definition E47 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0] 2%nat.
Definition E48 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0] 2%nat.
Definition E49 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0],1%nat)].
Definition E50 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0],1%nat)].
Definition E51 : Entry := EO [1;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0] [0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0] 1%nat.
Definition E52 : Entry := EB [([1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0],2%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E53 : Entry := EB [([1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0],2%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E54 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E55 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1] 0%nat.
Definition E56 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E57 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1] 0%nat.
Definition E58 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E59 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E60 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1] 0%nat.
Definition E61 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E62 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1] 0%nat.
Definition E63 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0] 1%nat.
Definition E64 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] 1%nat.
Definition E65 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0] 1%nat.
Definition E66 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 4%nat.
Definition E67 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;0;0;1;0;0;0;0;1] 0%nat.
Definition E68 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0],2%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;0;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;0;0;1;0;1;0;1;0],0%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0],4%nat)].
Definition E69 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],2%nat)].
Definition E70 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;1;0;0;0;0;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1] 1%nat.
Definition E71 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;1;0;0;1;0;0;1;0;0],5%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E72 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;0],8%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E73 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E74 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0] 1%nat.
Definition E75 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;1;0;0;1;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0] 2%nat.
Definition E76 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0] 1%nat.
Definition E77 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0],1%nat)].
Definition E78 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0],1%nat)].
Definition E79 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1] 0%nat.
Definition E80 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E81 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],4%nat)].
Definition E82 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1] 0%nat.
Definition E83 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],4%nat)].
Definition E84 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E85 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E86 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;1;0;0;0;0;0;0;0;0;1;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0] 1%nat.
Definition E87 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0] 1%nat.
Definition E88 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;0;0] 1%nat.
Definition E89 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0] 1%nat.
Definition E90 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0] 1%nat.
Definition E91 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0] 1%nat.
Definition E92 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E93 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E94 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0] 4%nat.
Definition E95 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E96 : Entry := EB [([1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0],1%nat); ([0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0],0%nat)] [([0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0],2%nat)].
Definition E97 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],2%nat)].
Definition E98 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0],2%nat)].
Definition E99 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E100 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E101 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0],6%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E102 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],6%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E103 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] 2%nat.
Definition E104 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0] 2%nat.
Definition E105 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0],1%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;0;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;0;0;1;0;0;0;0],0%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0],1%nat)].
Definition E106 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;0;0;0],1%nat)].
Definition E107 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0] 1%nat.
Definition E108 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0],2%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;1;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)].
Definition E109 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E110 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E111 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0],4%nat)].
Definition E112 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E113 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0],4%nat)].
Definition E114 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0],4%nat)].
Definition E115 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;0;0] 1%nat.
Definition E116 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0] 1%nat.
Definition E117 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0] 2%nat.
Definition E118 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E119 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E120 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0],2%nat)].
Definition E121 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0],2%nat)].
Definition E122 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0],2%nat)].
Definition E123 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],8%nat)].
Definition E124 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;0;0;0;1;0;1] 0%nat.
Definition E125 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] 2%nat.
Definition E126 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E127 : Entry := EH [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1].
Definition E128 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;0;0;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0],2%nat)].
Definition E129 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0],2%nat)].
Definition E130 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],8%nat)].
Definition E131 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E132 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],8%nat)].
Definition E133 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0;1;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;1;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0] 1%nat.
Definition E134 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 6%nat.
Definition E135 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 6%nat.
Definition E136 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0] 1%nat.
Definition E137 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],10%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],16%nat)].
Definition E138 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0] 1%nat.
Definition E139 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0],8%nat)].
Definition E140 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],6%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],8%nat)].
Definition E141 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0] 2%nat.
Definition E142 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0] 4%nat.
Definition E143 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E144 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],4%nat)].
Definition E145 : Entry := EO [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0] [0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0] 1%nat.
Definition E146 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;0],1%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;0;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0],2%nat)].
Definition E147 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0],2%nat)].
Definition E148 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],2%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],8%nat)].
Definition E149 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0],8%nat)].
Definition E150 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1] 0%nat.
Definition E151 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0] 1%nat.
Definition E152 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1] 1%nat.
Definition E153 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1] 0%nat.
Definition E154 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0] 4%nat.
Definition E155 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0] 2%nat.
Definition E156 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],8%nat)].
Definition E157 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;1;0;0;1;0;1] 0%nat.
Definition E158 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;0;0;0],6%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],16%nat)].
Definition E159 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],16%nat)].
Definition E160 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0],8%nat)].
Definition E161 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],12%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0],32%nat)].
Definition E162 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],20%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0],32%nat)].
Definition E163 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1] 2%nat.
Definition E164 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0],4%nat)].
Definition E165 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0] 6%nat.
Definition E166 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;0;0;0;0;0;0;0;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0],8%nat)].
Definition E167 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1] 0%nat.
Definition E168 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;0],1%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;0;0;0],3%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;0;0],4%nat)].
Definition E169 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;0],169%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],256%nat)].
Definition E170 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0],14%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0],32%nat)].
Definition E171 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0] 1%nat.
Definition E172 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;0;0;0],31%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],64%nat)].
Definition E173 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0] 2%nat.
Definition E174 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],2%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0],16%nat)].
Definition E175 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;0;0;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;1] 1%nat.
Definition E176 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0],6%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0],32%nat)].
Definition E177 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0] 3%nat.
Definition E178 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;0],1%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;1;0;1;0;0;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;1;0;1;0;0;0;0],2%nat)].
Definition E179 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],2%nat); ([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;0;0;1;0;1;0;1;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0],8%nat)].
Definition E180 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;0],5%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;0],8%nat)].
Definition E181 : Entry := EB [([1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;0],4%nat)] [([0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0],0%nat); ([1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0],16%nat)].
Definition E182 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;0;0;0;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0] 1%nat.
Definition E183 : Entry := EO [1;1;0;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0] [0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;1;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;1;0;0;0;0;0;1;0;1;0;1;0;1;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;0;1;0;1;0;1;0;0;0;0;0;1;0;1;0;0;0;0;1;0;0;1;0;1;0;0;0;0;0;0;0;1;0;0;1;0;1;0;0] 2%nat.

Definition STRIE : Trie := (TNode None (TNode (Some E0) (TNode None (TNode (Some E1) TNil TNil) (TNode None (TNode (Some E3) TNil TNil) (TNode None (TNode None (TNode (Some E5) TNil TNil) (TNode None (TNode (Some E9) TNil TNil) TNil)) TNil))) (TNode None (TNode None (TNode None (TNode None (TNode None (TNode (Some E10) TNil TNil) (TNode None (TNode None (TNode (Some E15) TNil TNil) (TNode None (TNode (Some E16) TNil TNil) TNil)) TNil)) TNil) (TNode None (TNode None (TNode None (TNode None (TNode None (TNode (Some E17) TNil TNil) (TNode None (TNode None (TNode (Some E20) TNil TNil) TNil) TNil)) TNil) (TNode None (TNode None (TNode None (TNode None (TNode None (TNode None (TNode (Some E28) TNil TNil) TNil) TNil) TNil) TNil) TNil) TNil)) (TNode None (TNode None (TNode None (TNode None (TNode None TNil (TNode None (TNode (Some E24) TNil TNil) TNil)) TNil) (TNode None (TNode None (TNode None (TNode (Some E25) TNil TNil) TNil) TNil) TNil)) (TNode None (TNode None (TNode None (TNode None (TNode (Some E26) TNil TNil) TNil) TNil) TNil) TNil)) TNil)) TNil)) (TNode None (TNode None (TNode (Some E6) TNil TNil) (TNode None (TNode (Some E11) TNil TNil) TNil)) (TNode None (TNode None (TNode None (TNode None (TNode None (TNode (Some E18) TNil TNil) TNil) TNil) (TNode None (TNode None (TNode None (TNode None (TNode None (TNode (Some E27) TNil TNil) TNil) TNil) TNil) TNil) TNil)) TNil) TNil))) TNil)) (TNode None (TNode None (TNode (Some E2) TNil TNil) (TNode None (TNode (Some E4) TNil TNil) (TNode None (TNode None (TNode (Some E7) TNil TNil) (TNode None (TNode (Some E12) TNil TNil) TNil)) TNil))) (TNode None (TNode None (TNode None (TNode None (TNode None (TNode (Some E13) TNil TNil) TNil) TNil) (TNode None (TNode None (TNode None TNil (TNode None (TNode None (TNode None (TNode None (TNode (Some E21) TNil TNil) TNil) TNil) TNil) TNil)) (TNode None (TNode None (TNode None (TNode None (TNode None (TNode (Some E22) TNil TNil) TNil) TNil) TNil) (TNode None (TNode None (TNode (Some E19) TNil TNil) (TNode None (TNode (Some E23) TNil TNil) TNil)) TNil)) TNil)) TNil)) (TNode None (TNode None (TNode (Some E8) TNil TNil) (TNode None (TNode (Some E14) TNil TNil) TNil)) TNil)) TNil))).
Definition LONGS : list Entry := [E29; E30; E31; E32; E33; E34; E35; E36; E37; E38; E39; E40; E41; E42; E43; E44; E45; E46; E47; E48; E49; E50; E51; E52; E53; E54; E55; E56; E57; E58; E59; E60; E61; E62; E63; E64; E65; E66; E67; E68; E69; E70; E71; E72; E73; E74; E75; E76; E77; E78; E79; E80; E81; E82; E83; E84; E85; E86; E87; E88; E89; E90; E91; E92; E93; E94; E95; E96; E97; E98; E99; E100; E101; E102; E103; E104; E105; E106; E107; E108; E109; E110; E111; E112; E113; E114; E115; E116; E117; E118; E119; E120; E121; E122; E123; E124; E125; E126; E127; E128; E129; E130; E131; E132; E133; E134; E135; E136; E137; E138; E139; E140; E141; E142; E143; E144; E145; E146; E147; E148; E149; E150; E151; E152; E153; E154; E155; E156; E157; E158; E159; E160; E161; E162; E163; E164; E165; E166; E167; E168; E169; E170; E171; E172; E173; E174; E175; E176; E177; E178; E179; E180; E181; E182; E183].
Lemma STRIE_ok : trie_all entry_ok STRIE = true.
Proof. vm_compute. reflexivity. Qed.
Lemma LONGS_ok : forallb entry_ok LONGS = true.
Proof. vm_compute. reflexivity. Qed.

Definition decode (w:list Sym) : option (Entry * list Sym) :=
 match walk STRIE w 14 None with
 | Some e =>
   let '(u,t) := take_pad (length (entry_u e)) w in
   if lsym_eqb u (entry_u e) then Some (e,t) else None
 | None => scan LONGS w
 end.
Lemma decode_sound w e t : decode w = Some (e,t) ->
 entry_ok e = true /\ w *> 0inf = entry_u e *> (t *> 0inf).
Proof.
 unfold decode. destruct (walk STRIE w 14 None) as [e0|] eqn:Ew.
 - pose proof (take_pad_sound (length (entry_u e0)) w) as Hw.
   revert Hw. destruct (take_pad (length (entry_u e0)) w) as [u t0]. cbn[fst snd]. intros Hw.
   cbn beta iota.
   destruct (lsym_eqb u (entry_u e0)) eqn:Eq; [|discriminate].
   intros H. injection H as <- <-. apply lsym_eqb_eq in Eq. subst u. split; [|exact Hw].
   eapply walk_ok; [exact STRIE_ok| |exact Ew]. intros x Hx; discriminate.
 - apply scan_ok, LONGS_ok.
Qed.

(* ---------------- the evaluator (valu42's shape; generic actions) ---------------- *)
Inductive Outcome := Unknown | Done (w:list Sym) | Halt.
Definition prepend (w:list Sym) (x:Outcome) :=
 match x with Done t => Done (w++t) | _ => x end.
Fixpoint eval (fuel:nat) (n:N) (w:list Sym) : Outcome :=
 match n with
 | N0 => Done w
 | Npos _ => match fuel with
   | O => Unknown
   | S fuel =>
     match decode w with
     | None => Unknown
     | Some (e,t) =>
       match e with
       | EB pre cyc => prepend (b_word pre cyc n) (eval fuel (b_out pre cyc n) t)
       | EO u v k =>
         match k with
         | O => eval fuel (N.pred n) (v++t)
         | S _ => match eval fuel (N.of_nat k) t with
                  | Done t' => eval fuel (N.pred n) (v++t')
                  | x => x
                  end
         end
       | EH u => Halt
       end
     end
   end
 end.
Definition denotes (w:list Sym) := w *> 0inf.
Definition Sem (n:N) (w:list Sym) (x:Outcome) : Prop :=
 match x with
 | Unknown => True
 | Done y => sideRLs tm (Calls n) (denotes w) (denotes y)
 | Halt => sideRLs_halt tm (Calls n) (denotes w)
 end.

(* valu42's soundness lemmas, unchanged *)
Lemma sem_input_eq n w w' x : denotes w = denotes w' -> Sem n w' x -> Sem n w x.
Proof. destruct x; cbn[Sem]; intros E H; [exact I|rewrite E|rewrite E]; assumption. Qed.
Lemma sem_segment n m u v t x :
 segRLs tm (Calls n) (Calls m) u v ->
 Sem m t x -> Sem n (u++t) (prepend v x).
Proof.
 destruct x; cbn[Sem prepend]; intros HS HX; [exact I| |]; unfold denotes in *;
 repeat rewrite Str_app_assoc;
 [eapply segRLs_sideRLs_concat | eapply segRLs_sideRLs_halt_concat]; eassumption.
Qed.
Lemma calls_addN n m : Calls (n+m)%N = Calls n ++ Calls m.
Proof. unfold Calls. rewrite N2Nat.inj_add,lpow_add. reflexivity. Qed.
Lemma sem_after n w u x :
 (0<n)%N -> sideRLs tm (Calls 1) (denotes w) (denotes u) ->
 Sem (N.pred n) u x -> Sem n w x.
Proof.
 intros Hn HS HX. replace n with (1+N.pred n)%N by lia.
 destruct x; cbn[Sem] in *; [exact I| |]; rewrite calls_addN;
 [eapply sideRLs_trans | eapply sideRLs_halt_app_right]; eassumption.
Qed.
Lemma sem_early n w : (0<n)%N -> Sem 1 w Halt -> Sem n w Halt.
Proof.
 intros Hn H. cbn[Sem] in *.
 replace n with (1+N.pred n)%N by lia.
 rewrite calls_addN. apply sideRLs_halt_app_left. exact H.
Qed.
Lemma packet_return u v t : segRLs tm (Calls 1) [] u v ->
 sideRLs tm (Calls 1) (denotes (u++t)) (denotes (v++t)).
Proof. intros H. unfold denotes. repeat rewrite Str_app_assoc.
 eapply segRLs_sideRLs_concat; [exact H|constructor]. Qed.
Lemma sem_single n u v t x : (0<n)%N -> segRLs tm (Calls 1) [] u v ->
 Sem (N.pred n) (v++t) x -> Sem n (u++t) x.
Proof. intros Hn H Hx. eapply sem_after; [exact Hn|eapply packet_return; exact H|exact Hx]. Qed.
Lemma sem_child n m u v t x f : (0<n)%N ->
 segRLs tm (Calls 1) (Calls m) u v ->
 Sem m t x ->
 (forall y, x=Done y -> Sem (N.pred n) (v++y) (f y)) ->
 Sem n (u++t) (match x with Unknown => Unknown | Done y => f y | Halt => Halt end).
Proof.
 intros Hn HS HX HF. destruct x; cbn[Sem] in *.
 - exact I.
 - apply (sem_after n (u++t) (v++w)); [exact Hn| |exact (HF w eq_refl)].
   unfold denotes. repeat rewrite Str_app_assoc. eapply segRLs_sideRLs_concat; eassumption.
 - apply sem_early; [exact Hn|]. cbn[Sem]. unfold denotes.
   rewrite Str_app_assoc. eapply segRLs_sideRLs_halt_concat; eassumption.
Qed.

(* Kestrel: soundness of the generic evaluator, in the pattern of valu42's eval_sound *)
Lemma calls_of_nat k : Calls (N.of_nat k) = h^^k.
Proof. unfold Calls. rewrite Nat2N.id. reflexivity. Qed.

Theorem eval_sound fuel n w : Sem n w (eval fuel n w).
Proof.
 revert n w. induction fuel as [|fuel IH]; intros n w.
 - destruct n; cbn[eval Sem Calls]; [constructor|exact I].
 - destruct n as [|p]; [cbn[eval Sem Calls]; constructor|].
   cbn[eval]. destruct (decode w) as [[e t]|] eqn:ED; [|exact I].
   destruct (decode_sound _ _ _ ED) as [Hok HD].
   apply (sem_input_eq _ w (entry_u e ++ t)).
   { unfold denotes. rewrite Str_app_assoc. exact HD. }
   destruct e as [pre cyc|u v k|u]; cbn[entry_u] in *.
   + eapply sem_segment; [apply (batch_law pre cyc Hok)|apply IH].
   + cbn[entry_ok] in Hok. apply law_ok_sound in Hok.
     destruct k as [|k'].
     * eapply sem_single; [lia|exact Hok|apply IH].
     * eapply (sem_child (Npos p) (N.of_nat (S k')) u v t (eval fuel (N.of_nat (S k')) t)
                (fun y => eval fuel (N.pred (Npos p)) (v++y))); [lia| |apply IH|].
       { rewrite calls_of_nat. exact Hok. }
       intros y E. apply IH.
   + apply sem_early; [lia|]. cbn[Sem Calls N.to_nat]. constructor. intro l.
     cbn[entry_ok] in Hok. apply lsym_eqb_eq in Hok. subst u.
     unfold denotes. rewrite Str_app_assoc. apply UH_halts.
Qed.

(* ---------------- the boundary and the orbit (valu42's, with this machine's seed) ---------------- *)
Definition boundary r := (A,(0inf,1,0>>r)).
Lemma boundary_entry r : boundary r -[tm]->* (0inf <*< [1]) {{{(hR,R)}}} [1;0] *> r.
Proof. unfold boundary,hR. esx. Qed.
Lemma boundary_return r : (0inf <*< [1]) {{{(hL,L)}}} r = boundary r.
Proof. reflexivity. Qed.
Lemma blank_seed : c0 -[tm]->* boundary ([1] *> 0inf).
Proof. unfold boundary. esx. Qed.
Fixpoint orbit (rounds fuel:nat) (w:list Sym) : bool :=
 match rounds with
 | O => false
 | S rounds' => match eval fuel 1%N ([1;0]++w) with
   | Unknown => false | Done u => orbit rounds' fuel u | Halt => true end
 end.
Lemma denotes_app u v : denotes (u++v) = u *> denotes v.
Proof. unfold denotes. apply Str_app_assoc. Qed.
Lemma boundary_done fuel w u : eval fuel 1%N ([1;0]++w) = Done u ->
 boundary (denotes w) -[tm]->* boundary (denotes u).
Proof.
 intro E. pose proof (eval_sound fuel 1%N ([1;0]++w)) as H.
 rewrite E in H. cbn[Sem Calls N.to_nat] in H. rewrite denotes_app in H.
 eapply evstep_trans; [apply boundary_entry|]. rewrite <- boundary_return.
 apply progress_evstep. apply sideRLs_1. exact H.
Qed.
Lemma boundary_halt fuel w : eval fuel 1%N ([1;0]++w) = Halt ->
 halts tm (boundary (denotes w)).
Proof.
 intro E. pose proof (eval_sound fuel 1%N ([1;0]++w)) as H.
 rewrite E in H. cbn[Sem Calls N.to_nat] in H. rewrite denotes_app in H.
 eapply halts_evstep; [|apply boundary_entry].
 eapply sideRLs_halt_single. exact H.
Qed.
Lemma orbit_halts rounds fuel w : orbit rounds fuel w = true ->
 halts tm (boundary (denotes w)).
Proof.
 revert w. induction rounds as [|rounds IH]; intros w H.
 - discriminate.
 - cbn[orbit] in H.
   destruct (eval fuel 1%N ([1;0]++w)) as [|u|] eqn:E.
   + discriminate.
   + eapply halts_evstep; [apply IH,H|]. eapply boundary_done; exact E.
   + apply boundary_halt with (fuel:=fuel). exact E.
Qed.
Lemma checked_orbit : orbit 2198 11250 [1] = true.
Proof. vm_compute. reflexivity. Qed.
Theorem halt : halts tm c0.
Proof.
 eapply halts_evstep; [|apply blank_seed].
 exact (orbit_halts 2198 11250 [1] checked_orbit).
Qed.
End TM1.
Print Assumptions TM1.halt.

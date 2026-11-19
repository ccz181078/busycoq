(* SOC23.TM165: standalone periodic-tape checker and halting proof.
   This file needs only BusyCoq and the standard library. *)
From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2 FastRev.
Require Import NArith ZArith PeanoNat Lia ZifyNat List String.

(* Machine-independent periodic counter arithmetic. *)
Import ListNotations.
Open Scope Z_scope.

Module Periodic2.
Definition bit (b:bool) : Z := if b then 1 else 0.
Definition pattern := (bool*bool)%type.
Definition digit (p:pattern) := bit (fst p)+2*bit (snd p).

Definition subbit (a b borrow:bool) :=
  (xorb (xorb a b) borrow,
   orb (andb (negb a) (orb b borrow)) (andb b borrow)).
Definition subpair (a b:pattern) borrow :=
  let '(lo,c):=subbit (fst a) (fst b) borrow in
  let '(hi,c'):=subbit (snd a) (snd b) c in ((lo,hi),c').
Lemma subbit_spec a b c:
  bit a-bit b-bit c=bit (fst (subbit a b c))-2*bit (snd (subbit a b c)).
Proof. destruct a,b,c; reflexivity. Qed.
Lemma subpair_spec a b c:
  digit a-digit b-bit c=digit (fst (subpair a b c))-4*bit (snd (subpair a b c)).
Proof. destruct a as [[] []],b as [[] []],c; reflexivity. Qed.
Lemma borrow_stable a b c:
  snd (subpair a b (snd (subpair a b c)))=snd (subpair a b c).
Proof. destruct a as [[] []],b as [[] []],c; reflexivity. Qed.

(* Semantic-only powers and repeated digits. Counts in executable data are N. *)
Fixpoint radix n : Z := match n with O=>1 | S n=>4*radix n end.
Fixpoint tile p n : Z := match n with O=>0 | S n=>digit p+4*tile p n end.
Lemma radix_pos n: 0<radix n.
Proof. induction n; cbn [radix]; lia. Qed.
Lemma digit_bounds p: 0<=digit p<=3.
Proof. destruct p as [[] []]; unfold digit,bit; cbn [fst snd]; lia. Qed.
Lemma tile_bounds p n: 0<=tile p n<radix n.
Proof. induction n; cbn [tile radix]; pose proof (digit_bounds p); lia. Qed.
Lemma tile_split p n m: tile p (n+m)=tile p n+radix n*tile p m.
Proof. induction n; cbn [Nat.add tile radix]; rewrite ?IHn; ring. Qed.
Lemma radix_add n m: radix (n+m)=radix n*radix m.
Proof. induction n; cbn [Nat.add radix]; rewrite ?IHn; ring. Qed.

Lemma tile_stable a b c out n: subpair a b c=(out,c) ->
  tile a n-tile b n-bit c=tile out n-radix n*bit c.
Proof.
  intro H; pose proof (subpair_spec a b c) as E; rewrite H in E; cbn [fst snd] in E.
  induction n; cbn [tile radix]; nia.
Qed.
Lemma tile_sub a b c n:
  let '(first,carry):=subpair a b c in
  let stable:=fst (subpair a b carry) in
  tile a (S n)-tile b (S n)-bit c=
    digit first+4*tile stable n-radix (S n)*bit carry.
Proof.
  pose proof (subpair_spec a b c) as E; pose proof (borrow_stable a b c) as Hc.
  destruct (subpair a b c) as [first carry] eqn:H; cbn [fst snd] in *.
  destruct (subpair a b carry) as [stable carry'] eqn:Hs; cbn [fst snd] in *; subst carry'.
  pose proof (tile_stable a b carry stable n Hs).
  cbn [tile radix]; nia.
Qed.

(* The runtime may cut a period after one bit.  These identities cover both
   parities, including the last ordinary borrow after a repeated block. *)
Definition swap (p:pattern) := (snd p,fst p).
Fixpoint alt p n : Z := match n with
  | O=>0 | S n=>bit (fst p)+2*alt (swap p) n end.
Lemma swap_swap p: swap (swap p)=p.
Proof. destruct p; reflexivity. Qed.
Lemma alt_pair p n: alt p (S (S n))=digit p+4*alt p n.
Proof. cbn [alt]; rewrite swap_swap; unfold digit,swap; cbn [fst snd]; ring. Qed.
Lemma alt_even p n: alt p (n+n)=tile p n.
Proof.
  induction n; [reflexivity|].
  replace (S n+S n)%nat with (S (S (n+n))) by lia.
  rewrite alt_pair,IHn; reflexivity.
Qed.
Lemma alt_odd p n: alt p (S (n+n))=tile p n+radix n*bit (fst p).
Proof.
  induction n; [cbn [Nat.add alt tile radix]; ring|].
  replace (S (S n+S n)) with (S (S (S (n+n)))) by lia.
  rewrite alt_pair,IHn; cbn [tile radix]; ring.
Qed.
Lemma alt_sub_even a b c n:
  let '(first,carry):=subpair a b c in
  alt a (S n+S n)-alt b (S n+S n)-bit c=
    digit first+4*tile (fst (subpair a b carry)) n-radix (S n)*bit carry.
Proof. rewrite !alt_even; apply tile_sub. Qed.
Lemma alt_sub_odd a b c n:
  let '(first,carry):=subpair a b c in
  let '(last,carry'):=subbit (fst a) (fst b) carry in
  alt a (S (S n+S n))-alt b (S (S n+S n))-bit c=
    digit first+4*tile (fst (subpair a b carry)) n+
      radix (S n)*bit last-2*radix (S n)*bit carry'.
Proof.
  pose proof (tile_sub a b c n) as H.
  destruct (subpair a b c) as [first carry]; cbn [fst snd] in H |- *.
  pose proof (subbit_spec (fst a) (fst b) carry) as E.
  destruct (subbit (fst a) (fst b) carry) as [last carry']; cbn [fst snd] in E |- *.
  rewrite !alt_odd; nia.
Qed.
Lemma tile_difference a b n:
  3*(tile a n-tile b n)=(radix n-1)*(digit a-digit b).
Proof. induction n; cbn [tile radix]; nia. Qed.
Lemma tile_order a b n: (0<n)%nat ->
  (tile a n<tile b n <-> digit a<digit b).
Proof.
  destruct n; [lia|]; intros _.
  pose proof (tile_difference a b (S n)); pose proof (radix_pos n).
  cbn [radix] in *; split; nia.
Qed.

Record run := Run { bits:pattern; count:N }.
Fixpoint value xs := match xs with
  | []=>0 | Run p n::xs=>tile p (N.to_nat n)+radix (N.to_nat n)*value xs end.
Definition subtract_block a b c n :=
  if N.eqb n 0 then ([],c) else
  let '(first,carry):=subpair a b c in
  ([Run first 1; Run (fst (subpair a b carry)) (n-1)],carry).
Lemma subtract_block_spec a b c n:
  tile a (N.to_nat n)-tile b (N.to_nat n)-bit c=
    value (fst (subtract_block a b c n))-radix (N.to_nat n)*bit (snd (subtract_block a b c n)).
Proof.
  unfold subtract_block; destruct (N.eqb n 0) eqn:Hn.
  - apply N.eqb_eq in Hn; subst; change (0-0-bit c=0-1*bit c); ring.
  - apply N.eqb_neq in Hn.
    pose proof (tile_sub a b c (N.to_nat (n-1))) as H.
    destruct (subpair a b c) as [first carry]; cbn [fst snd value] in *.
    replace (N.to_nat n) with (S (N.to_nat (n-1))) by lia.
    change (N.to_nat 1) with 1%nat; cbn [tile radix] in H |- *; nia.
Qed.

Lemma subtract_block_append a b c n tail:
  tile a (N.to_nat n)-tile b (N.to_nat n)-bit c+radix (N.to_nat n)*tail=
  value (fst (subtract_block a b c n))+
    radix (N.to_nat n)*(tail-bit (snd (subtract_block a b c n))).
Proof. pose proof (subtract_block_spec a b c n); nia. Qed.
End Periodic2.

(* Executable periodic backend; soundness is proved below. *)
Import ListNotations.
Open Scope N_scope.

(* Pure finite memoization, not a mutable table or an execution trace. *)
Module ShortCache.
Inductive tree (A:Type) := Leaf (value:A) | Fork (zero one:tree A).
Arguments Leaf {A} _.
Arguments Fork {A} _ _.
Fixpoint build {A} k (f:N->A) := match k with
| O=>Leaf (f 0)
| S k=>Fork (build k (fun n=>f (2*n))) (build k (fun n=>f (2*n+1))) end.
Fixpoint get {A} n (t:tree A) := match t with
| Leaf a=>a | Fork l r=>if N.odd n then get (N.div2 n) r else get (N.div2 n) l end.
Lemma get_build {A} k (f:N->A) n: n<2^N.of_nat k -> get n (build k f)=f n.
Proof.
  revert f n; induction k as [|k IH]; intros f n H.
  - assert (n=0) by (cbn in H; lia); subst; reflexivity.
  - rewrite Nat2N.inj_succ,N.pow_succ_r' in H.
    pose proof (N.div2_odd n) as E.
    cbn [build get]; destruct (N.odd n) eqn:B; rewrite IH by lia;
      f_equal; cbn [N.b2n] in E; lia.
Qed.
Definition table {A} (f:N->nat->A) := build 4 (fun w=>build 8 (fun p=>f p (N.to_nat w))).
Definition cached {A} (f:N->nat->A) (t:tree (tree A)) p w :=
  if Nat.leb w 15 then if N.ltb p 256 then get p (get (N.of_nat w) t) else f p w else f p w.
Lemma cached_spec {A} (f:N->nat->A) p w: cached f (table f) p w=f p w.
Proof.
  unfold cached,table.
  destruct (Nat.leb_spec0 w 15); [|reflexivity].
  destruct (N.ltb_spec p 256); [|reflexivity].
  rewrite (get_build 4 _ (N.of_nat w)) by (change (N.of_nat w<16); lia).
  rewrite (get_build 8 _ p) by (change (p<256); assumption).
  now rewrite Nat2N.id.
Qed.
End ShortCache.

Module PeriodicRuntime.
Record block := Bl { pat:N; width:nat; len:N }.
Definition stack := list block.
Definition mask w := N.shiftl 1 (N.of_nat w)-1.
Definition rot1 w p := N.div2 p + if N.odd p then N.shiftl 1 (N.of_nat (w-1)) else 0.
Fixpoint rotate_small p w n := match n with
  | O=>p | S n=>rotate_small (rot1 w p) w n end.
Definition rotate p w n := rotate_small p w (N.to_nat (n mod N.of_nat w)).
Fixpoint prefix p w n := match n with
  | O=>0 | S n=>N.b2n (N.odd p)+2*prefix (rot1 w p) w n end.
Fixpoint reduce_search (ds:list nat) (p:N) (w:nat) := match ds with
  | []=>(p,w)
  | d::ds=>if Nat.eqb (Nat.modulo w d) 0 then
      let q:=N.land p (mask d) in
      if N.eqb (prefix q d w) p then (q,d) else reduce_search ds p w
    else reduce_search ds p w end.
Definition reduce_info p w := reduce_search [1;2;3;4;5;6;7]%nat p w.
Definition reduce_table := ShortCache.table reduce_info.
Definition reduce b := let '(p,w):=ShortCache.cached reduce_info reduce_table (pat b) (width b) in
  Bl p w (len b).
Definition short_eq p w q v n := N.eqb (prefix p w (N.to_nat n)) (prefix q v (N.to_nat n)).
Definition merge a b :=
  if andb (Nat.eqb (width a) (width b)) (N.eqb (rotate (pat a) (width a) (len a)) (pat b))
  then Some (Bl (pat a) (width a) (len a+len b)) else
  if andb (N.leb (len a) 8) (N.leb (N.of_nat (width b)) (len b)) then
    let p:=rotate (pat b) (width b) (N.of_nat (width b)-len a mod N.of_nat (width b)) in
    if short_eq p (width b) (pat a) (width a) (len a)
    then Some (Bl p (width b) (len a+len b)) else None
  else None.
Definition merge_more a b := match merge a b with
  | Some c=>Some c
  | None=>if andb (N.leb (len b) 8) (N.leb (N.of_nat (width a)) (len a)) then
      if short_eq (rotate (pat a) (width a) (len a)) (width a) (pat b) (width b) (len b)
      then Some (Bl (pat a) (width a) (len a+len b)) else None
    else None end.
Definition join a b := match merge_more a b with
  | Some c=>Some c
  | None=>if N.leb (len a+len b) 8 then
      Some (Bl (N.lor (prefix (pat a) (width a) (N.to_nat (len a)))
        (N.shiftl (prefix (pat b) (width b) (N.to_nat (len b))) (len a)))
        (N.to_nat (len a+len b)) (len a+len b)) else None end.
Fixpoint push_join b s := match s with
  | []=>if N.eqb (pat b) 0 then [] else [b]
  | a::s'=>match join b a with
    | Some c=>push_join (reduce c) s' | None=>b::s end end.
Definition push p w n s := if N.eqb n 0 then s else push_join (reduce (Bl (N.land p (mask w)) w n)) s.
Fixpoint drop n s := match s with
  | []=>[] | b::s'=>if N.leb (len b) n then drop (n-len b) s'
    else Bl (rotate (pat b) (width b) n) (width b) (len b-n)::s' end.
Definition top s := match s with []=>0 | b::_=>N.b2n (N.odd (pat b)) end.
Fixpoint peek n s := match n with
  | O=>0 | S n=>top s+2*peek n (drop 1 s) end.
Definition push1 b := push b 1 1.

Fixpoint count_rec fuel p w limit s := match fuel with
  | O=>0 | S fuel=>if N.eqb limit 0 then 0 else
    let bulk:=match s with
      | []=>0 | b::_=>let per:=Nat.lcm w (width b) in
        if andb (N.leb (N.of_nat per) (len b))
          (N.eqb (prefix (pat b) (width b) per) (prefix p w per))
        then N.min limit (len b/N.of_nat w) else 0 end in
    if N.eqb bulk 0 then
      if N.eqb (peek w s) p then 1+count_rec fuel p w (limit-1) (drop (N.of_nat w) s) else 0
    else bulk+count_rec fuel p w (limit-bulk) (drop (bulk*N.of_nat w) s) end.
Definition count_budget := 1024%nat.
Definition count p w := count_rec count_budget p w 16384.

(* Counter parts store total bit lengths, not numbers of pairs. *)
Definition part := (N*N)%type.
Definition rot2 p n := if N.odd n then N.div2 p+2*N.b2n (N.odd p) else p.
Definition samepart p q n := if N.eqb n 1 then Bool.eqb (N.odd p) (N.odd q) else N.eqb p q.
Definition add_part p n acc := if N.eqb n 0 then acc else
  let p:=if N.eqb n 1 then if N.odd p then 3 else 0 else p in
  match acc with
  | []=>[(p,n)]
  | (a,k)::rest=>if samepart (rot2 a k) p n then (a,k+n)::rest else
      if N.eqb k 1 then
        let q:=rot2 p 1 in
        if Bool.eqb (N.odd q) (N.odd a) then (q,n+1)::rest else
        if N.eqb n 1 then (N.b2n (N.odd a)+2*N.b2n (N.odd p),2)::rest
        else (p,n)::acc
      else (p,n)::acc end.
Fixpoint trim_rev xs := match xs with
  | []=>[] | (p,n)::xs=>if N.eqb p 0 then trim_rev xs else
    if N.odd (rot2 p (n-1)) then (p,n)::xs else
    if N.eqb n 1 then xs else (p,n-1)::xs end.
Fixpoint bsize (xs:list part) := match xs with []=>0 | (_,n)::xs=>n+bsize xs end.
Definition end2 p n := rot2 p (n-1).
Definition cut_high (p:N) k n xs := if N.eqb k n then xs else (p,k-n)::xs.
Fixpoint compare_rec fuel xs ys := match fuel with
  | O=>Eq
  | S fuel=>match xs,ys with
    | [],[]=>Eq | [],_=>Lt | _,[]=>Gt
    | (p,k)::xs,(q,l)::ys=>
      let n:=N.min k l in
      let a:=end2 p k in let b:=end2 q l in
      let c:=N.compare (N.b2n (N.odd a)) (N.b2n (N.odd b)) in
      let c:=if andb (match c with Eq=>true|_=>false end) (N.ltb 1 n)
        then N.compare (N.div2 a) (N.div2 b) else c in
      match c with Eq=>compare_rec fuel (cut_high p k n xs) (cut_high q l n ys) | _=>c end
    end end.
Definition compare xs ys := match N.compare (bsize xs) (bsize ys) with
  | Eq=>compare_rec (S (List.length xs+List.length ys)) (fast_rev xs) (fast_rev ys)
  | c=>c end.
Definition to_pair p := (N.odd p,N.odd (N.div2 p)).
Definition from_pair (p:bool*bool) := N.b2n (fst p)+2*N.b2n (snd p).
Definition minus_pair p q c :=
  let '(v,c):=Periodic2.subpair (to_pair p) (to_pair q) c in (from_pair v,c).
Definition minus_bit p q c :=
  let '(v,c):=Periodic2.subbit (N.odd p) (N.odd q) c in (N.b2n v,c).
Definition subtract_part p q c n acc :=
  if N.eqb n 1 then let '(v,c):=minus_bit p q c in (add_part v 1 acc,c) else
  let '(v,c):=minus_pair p q c in
  let acc:=add_part v 2 acc in let n:=n-2 in
  let '(v,c):=minus_pair p q c in
  let acc:=add_part v (N.double (N.div2 n)) acc in
  if N.odd n then let '(v,c):=minus_bit p q c in (add_part v 1 acc,c) else (acc,c).
Definition cut_low p k n xs := if N.eqb k n then xs else (rot2 p n,k-n)::xs.
(* Comparison is only a proposal. A successful subtraction independently
   checks that all input was consumed and that no borrow remains. *)
Fixpoint subtract_rec fuel xs ys (c:bool) acc := match fuel with
  | O=>None | S fuel=>match xs with
    | []=>match ys with []=>if c then None else Some acc | _=>None end
    | (p,k)::xs=>let '(q,l,tail):=match ys with []=>(0,k,[]) | (q,l)::ys=>(q,l,ys) end in
      let n:=N.min k l in let '(acc,c):=subtract_part p q c n acc in
      subtract_rec fuel (cut_low p k n xs) (cut_low q l n tail) c acc
    end end.
Definition subtract xs ys := option_map (fun zs=>fast_rev (trim_rev zs))
  (subtract_rec (S (List.length xs+List.length ys)) xs ys false []).

Definition fixed stride := if Nat.eqb stride 2 then 2 else 0.
Fixpoint digits_ok fuel p w stride bp i := match fuel with
  | O=>true | S fuel=>let z:=prefix p w stride in
    if N.eqb (N.land z (mask stride-1)) (fixed stride) then
    if Bool.eqb (negb (N.odd z)) (N.odd (rot2 bp i))
    then digits_ok fuel (rotate p w (N.of_nat stride)) w stride bp (i+1)
    else false else false end.
Definition bulk_info stride p w :=
  let per:=Nat.lcm stride w in
    let a:=negb (N.odd p) in
    let c:=negb (N.odd (rotate p w (N.of_nat stride))) in
    let bp:=N.b2n a+2*N.b2n c in
    let d:=Nat.div per stride in
    (N.of_nat per, if andb (digits_ok d p w stride bp 0)
       (if Nat.odd d then Bool.eqb a c else true) then Some bp else None).
Definition bulk_table2 := ShortCache.table (bulk_info 2).
Definition bulk_table3 := ShortCache.table (bulk_info 3).
Definition bulk_cached stride p w := match stride with
  | 2%nat=>ShortCache.cached (bulk_info 2) bulk_table2 p w
  | 3%nat=>ShortCache.cached (bulk_info 3) bulk_table3 p w
  | _=>bulk_info stride p w end.
Lemma bulk_cached_spec stride p w: bulk_cached stride p w=bulk_info stride p w.
Proof.
  destruct stride as [|[|[|[|stride]]]]; try reflexivity;
    unfold bulk_cached,bulk_table2,bulk_table3; apply ShortCache.cached_spec.
Qed.
Definition bulk_pattern b stride :=
  let '(need,result):=bulk_cached stride (pat b) (width b) in
  if N.leb need (len b) then result else None.
Fixpoint parse_rec fuel stride limit s acc done := match fuel with
  | O=>(fast_rev (trim_rev acc),done)
  | S fuel=>if N.eqb limit 0 then (fast_rev (trim_rev acc),done) else
    match s with
    | []=>if Nat.eqb stride 3 then (fast_rev (trim_rev (add_part 3 limit acc)),done+limit)
      else (fast_rev (trim_rev acc),done)
    | b::_=>match bulk_pattern b stride with
      | Some p=>let n:=N.min limit (len b/N.of_nat stride) in
        parse_rec fuel stride (limit-n) (drop (n*N.of_nat stride) s) (add_part p n acc) (done+n)
      | None=>let z:=peek stride s in
        if N.eqb (N.land z (mask stride-1)) (fixed stride) then
          parse_rec fuel stride (limit-1) (drop (N.of_nat stride) s)
            (add_part (N.b2n (negb (N.odd z))) 1 acc) (done+1)
        else (fast_rev (trim_rev acc),done)
      end end end.
(* Share the unary budget; do not rebuild decimal-to-nat at every call. *)
Definition parse_budget := 131072%nat.
Definition parse stride limit s := parse_rec parse_budget stride limit s [] 0.
Definition physical p stride :=
  let d b:=fixed stride+N.b2n (negb b) in
  d (N.odd p)+N.shiftl (d (N.odd (N.div2 p))) (N.of_nat stride).
Fixpoint put_parts xs stride s := match xs with
  | []=>s | (p,n)::xs=>push (physical p stride) (2*stride)%nat (n*N.of_nat stride) (put_parts xs stride s) end.
Definition put xs n stride s := put_parts xs stride
  (push (physical 0 stride) (2*stride)%nat ((n-bsize xs)*N.of_nat stride) (drop (n*N.of_nat stride) s)).

Definition state := (Q*stack*stack)%type.
Definition pair qr (s:state) : option state := let '(q,l,r):=s in
  if q_eqb q qr then if N.eqb (peek 2 l) 2 then if N.eqb (N.land (peek 3 r) 6) 0 then
    let '(a,n):=parse 2 100000000 (drop 2 l) in
    match a with []=>None | _=>
    let '(b,k):=parse 3 (n+1) r in
    match b with []=>None | _=>
      let proposal:=match compare a b with
        | Lt=>option_map (fun b'=>([],b')) (subtract b a)
        | _=>option_map (fun a'=>(a',[])) (subtract a b) end in
      match proposal with
      | Some(a,b)=>Some(q,push 2 2 2 (put a n 2 (drop 2 l)),put b k 3 r)
      | None=>None end
    end end else None else None else None.

Record shift := Sh { sq:Q; sd:dir; sw:nat; sin:N; sout:N }.
Definition try_shift h (s:state) : option state := let '(q,l,r):=s in
  if q_eqb q (sq h) then match sd h with
    | R=>let n:=count (sin h) (sw h) r in
      if N.ltb 1 n then Some(q,push (sout h) (sw h) (n*N.of_nat (sw h)) l,drop (n*N.of_nat (sw h)) r) else None
    | L=>let l:=push1 (top r) l in let n:=count (sin h) (sw h) l in
      if N.ltb 1 n then let l:=drop (n*N.of_nat (sw h)) l in
        Some(q,drop 1 l,push1 (top l) (push (sout h) (sw h) (n*N.of_nat (sw h)) (drop 1 r))) else None
    end else None.
Fixpoint scan hs s := match hs with
  | []=>None | h::hs=>match try_shift h s with Some t=>Some t | None=>scan hs s end end.
Definition primitive tm (s:state) : option state := let '(q,l,r):=s in
  match tm (q,if N.eqb (top r) 0 then S0 else S1) with
  | None=>None | Some(b,d,q)=>let b:=match b with S0=>0 | S1=>1 end in
    let r:=drop 1 r in match d with
    | R=>Some(q,push1 b l,r)
    | L=>Some(q,drop 1 l,push1 (top l) (push1 b r)) end end.
Definition a_sweep qa (s:state) := let '(q,l,r):=s in
  if N.eqb (peek 1 (drop 1 r)) 1 then try_shift (Sh qa L 1 1 1) s else None.
Definition event tm qr hs s := match pair qr s with
  | Some t=>(1%nat,Some t)
  | None=>match scan hs s with
    | Some t=>(2%nat,Some t)
    | None=>match primitive tm s with Some t=>(3%nat,Some t) | None=>(4%nat,None) end end end.
End PeriodicRuntime.

(* Semantics of the experimental periodic tape, independent of a machine. *)
Import ListNotations PeriodicRuntime.
Open Scope N_scope.

Module PeriodicTape.
Definition sym (b:bool) : Sym := if b then S1 else S0.
Definition digit (b:Sym) : N := match b with S0=>0 | S1=>1 end.
Fixpoint code (xs:list Sym) : N := match xs with []=>0 | x::xs=>digit x+2*code xs end.
Fixpoint bits p w n : list Sym := match n with
  | O=>[] | S n=>sym (N.odd p)::bits (rot1 w p) w n end.
Definition good p w := (1<=w<=8)%nat /\ p<=mask w.
Definition goodb p w := andb (andb (Nat.leb 1 w) (Nat.leb w 8)) (N.leb p (mask w)).

Lemma goodb_spec p w: goodb p w=true <-> good p w.
Proof. unfold goodb,good; rewrite !Bool.andb_true_iff,!Nat.leb_le,N.leb_le; tauto. Qed.
Lemma code_inj xs ys: List.length xs=List.length ys -> code xs=code ys -> xs=ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hlen Hcode; try discriminate; [reflexivity|].
  cbn [List.length] in Hlen; cbn [code] in Hcode.
  destruct x,y; cbn [digit] in Hcode; try lia; f_equal; apply IH; lia.
Qed.
Lemma bits_length p w n: List.length (bits p w n)=n.
Proof. revert p; induction n; intros; cbn [bits List.length]; auto. Qed.
Lemma bits_code p w n: code (bits p w n)=prefix p w n.
Proof.
  revert p; induction n; intros; cbn [bits code prefix]; [reflexivity|].
  rewrite IHn; unfold sym; destruct (N.odd p); reflexivity.
Qed.
Lemma prefix_eq p w q v n: prefix p w n=prefix q v n -> bits p w n=bits q v n.
Proof. intro H; apply code_inj; [rewrite !bits_length|rewrite !bits_code]; auto. Qed.
Lemma bits_add p w n m:
  bits p w (n+m)=bits p w n++bits (rotate_small p w n) w m.
Proof. revert p; induction n; intros; cbn [Nat.add bits rotate_small]; rewrite ?IHn; reflexivity. Qed.
Lemma rotate_small_add p w n m:
  rotate_small p w (n+m)=rotate_small (rotate_small p w n) w m.
Proof. revert p; induction n; intros; cbn [Nat.add rotate_small]; auto. Qed.

(* A finite check establishes facts about all 2048 possible short words;
   arbitrary block lengths are handled by the generic lemmas below. *)
Definition short_check f := forallb (fun w=>forallb (fun k=>
  if goodb (N.of_nat k) w then f (N.of_nat k) w else true) (seq 0 256)) (seq 1 8).
Lemma short_check_spec f: short_check f=true -> forall p w, good p w -> f p w=true.
Proof.
  intros H p w [Hw Hp]; unfold short_check in H.
  rewrite forallb_forall in H; specialize (H w ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H.
  assert (Hmask: mask w<=255) by
    (destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try lia; vm_compute; discriminate).
  specialize (H (N.to_nat p) ltac:(apply in_seq; lia)).
  rewrite N2Nat.id in H.
  assert (G: goodb p w=true) by (apply goodb_spec; split; assumption).
  rewrite G in H; exact H.
Qed.
Definition word_check p w :=
  andb (goodb (rot1 w p) w) (andb (N.eqb (rotate_small p w w) p) (N.eqb (prefix p w w) p)).
Lemma word_checked: short_check word_check=true.
Proof. native_check_eq. Qed.
Lemma word_facts p w: good p w ->
  good (rot1 w p) w /\ rotate_small p w w=p /\ prefix p w w=p.
Proof.
  intro H; pose proof (short_check_spec _ word_checked p w H) as E.
  unfold word_check in E; rewrite !Bool.andb_true_iff,!N.eqb_eq,goodb_spec in E; exact E.
Qed.
Lemma rotate_small_good p w n: good p w -> good (rotate_small p w n) w.
Proof. revert p; induction n; intros p H; [exact H|apply IHn,word_facts,H]. Qed.
Lemma rotate_multiple p w n: rotate_small p w w=p -> rotate_small p w (n*w)=p.
Proof.
  intro H; induction n; [reflexivity|].
  change (rotate_small p w (w+n*w)=p); rewrite rotate_small_add,H; exact IHn.
Qed.
Lemma rotate_mod p w n: good p w -> rotate_small p w n=rotate_small p w (n mod w).
Proof.
  intros H; pose proof (word_facts _ _ H) as [_ [E _]]; destruct H as [Hw Hp].
  replace n with ((n/w)*w+n mod w)%nat at 1 by (pose proof (Nat.div_mod n w ltac:(lia)); lia).
  rewrite rotate_small_add,rotate_multiple; auto.
Qed.
Lemma rotate_spec p w n: good p w -> rotate p w n=rotate_small p w (N.to_nat n).
Proof.
  intro H; unfold rotate; rewrite N2Nat.inj_mod,Nat2N.id; symmetry; apply rotate_mod,H.
Qed.
Lemma rotate_good p w n: good p w -> good (rotate p w n) w.
Proof. intro H; rewrite rotate_spec by exact H; apply rotate_small_good,H. Qed.
Lemma bits_split p w n m: good p w ->
  bits p w (N.to_nat (n+m))=bits p w (N.to_nat n)++bits (rotate p w n) w (N.to_nat m).
Proof. intro H; rewrite N2Nat.inj_add,bits_add,rotate_spec by exact H; reflexivity. Qed.

Lemma bits_firstn p w n m: (n<=m)%nat -> firstn n (bits p w m)=bits p w n.
Proof.
  revert p m; induction n; intros p [|m] H; try (solve [cbn [firstn bits]; reflexivity|lia]).
  cbn [bits firstn]; f_equal; apply IHn; lia.
Qed.
Lemma same_period p w q v d: (0<d)%nat ->
  rotate_small p w d=p -> rotate_small q v d=q -> bits p w d=bits q v d ->
  forall n, bits p w n=bits q v n.
Proof.
  intros Hd Hp Hq Hbits n; induction n using strong_induction.
  destruct (Nat.leb_spec0 d n) as [Hle|Hle].
  - replace n with (d+(n-d))%nat by lia.
    rewrite !bits_add,Hp,Hq,Hbits; f_equal; apply H; lia.
  - apply (f_equal (firstn n)) in Hbits; rewrite !bits_firstn in Hbits by lia; exact Hbits.
Qed.
Definition reduced_check p w :=
  let '(q,v):=reduce_search [1;2;3;4;5;6;7]%nat p w in
  andb (goodb q v) (andb (N.eqb (rotate_small q v w) q) (N.eqb (prefix q v w) p)).
Lemma reduced_checked: short_check reduced_check=true.
Proof. native_check_eq. Qed.
Lemma reduce_spec p w n: good p w ->
  let b:=reduce (Bl p w n) in
  good (pat b) (width b) /\ len b=n /\ forall k, bits (pat b) (width b) k=bits p w k.
Proof.
  intro H; pose proof (word_facts _ _ H) as [_ [Hp Hprefix]].
  pose proof (short_check_spec _ reduced_checked p w H) as E.
  unfold reduced_check in E; unfold reduce,reduce_table; rewrite ShortCache.cached_spec.
  unfold reduce_info; cbn [pat width len].
  destruct (reduce_search [1;2;3;4;5;6;7]%nat p w) as [q v]; cbn [pat width len].
  rewrite !Bool.andb_true_iff,!N.eqb_eq,goodb_spec in E.
  destruct E as [G [Hq Eq]]; repeat split; try (apply G); try reflexivity.
  apply same_period with (d:=w); try assumption; [destruct H; lia|].
  apply prefix_eq; congruence.
Qed.
Definition back_check p w := forallb (fun k=>
  let n:=N.of_nat k in let q:=rotate p w (N.of_nat w-n mod N.of_nat w) in
  andb (goodb q w) (N.eqb (rotate q w n) p)) (seq 0 9).
Lemma back_checked: short_check back_check=true.
Proof. native_check_eq. Qed.
Lemma back_spec p w n: good p w -> n<=8 ->
  let q:=rotate p w (N.of_nat w-n mod N.of_nat w) in good q w /\ rotate q w n=p.
Proof.
  intros H Hn; pose proof (short_check_spec _ back_checked p w H) as E.
  unfold back_check in E; rewrite forallb_forall in E.
  specialize (E (N.to_nat n) ltac:(apply in_seq; lia)); rewrite N2Nat.id in E.
  rewrite Bool.andb_true_iff,goodb_spec,N.eqb_eq in E; exact E.
Qed.
Lemma mask_good p w: (1<=w<=8)%nat -> good (N.land p (mask w)) w.
Proof. intro H; split; [exact H|apply N.land_le_r]. Qed.
Lemma bits_zero w n: bits 0 w n=List.repeat S0 n.
Proof. induction n; [reflexivity|change (S0::bits 0 w n=S0::List.repeat S0 n); congruence]. Qed.
Lemma bits_skipn p w n m: (n<=m)%nat ->
  skipn n (bits p w m)=bits (rotate_small p w n) w (m-n).
Proof.
  revert p m; induction n; intros p [|m] H; try lia.
  all: cbn [Nat.sub skipn bits rotate_small]; auto; apply IHn; lia.
Qed.

Definition block_bits b := bits (pat b) (width b) (N.to_nat (len b)).
Definition good_block b := good (pat b) (width b) /\ 0<len b.
Definition valid := Forall good_block.
Fixpoint expand s := match s with []=>[] | b::s=>block_bits b++expand s end.
Definition denote s := expand s *> 0inf.
Lemma denote_cons b s: denote (b::s)=block_bits b *> denote s.
Proof. unfold denote; cbn [expand]; apply Str_app_assoc. Qed.
Lemma block_length b: List.length (block_bits b)=N.to_nat (len b).
Proof. apply bits_length. Qed.
Lemma reduce_block b: good_block b -> good_block (reduce b) /\ block_bits (reduce b)=block_bits b.
Proof.
  destruct b as [p w n]; intros [H Hn]; cbn [pat width len] in H,Hn.
  destruct (reduce_spec p w n H) as [G [E K]].
  split; [split; [exact G|rewrite E; exact Hn]|unfold block_bits; rewrite E; apply K].
Qed.
Lemma drop_valid s n: valid s -> valid (drop n s).
Proof.
  intros H; revert n; induction H as [|b s [Hb Hn] Hs IH]; intro n; [constructor|].
  cbn [drop]; destruct (N.leb (len b) n) eqn:E; [apply IH|].
  apply N.leb_gt in E; constructor; [split|exact Hs].
  - cbn [pat width]; apply rotate_good,Hb.
  - cbn [len]; lia.
Qed.
Lemma drop_expand s n: valid s -> expand (drop n s)=skipn (N.to_nat n) (expand s).
Proof.
  intros H; revert n; induction H as [|b s [Hb Hn] Hs IH]; intro n.
  - cbn [drop expand]; symmetry; apply skipn_nil.
  - cbn [drop expand]; destruct (N.leb (len b) n) eqn:E; rewrite skipn_app,block_length.
    + apply N.leb_le in E; rewrite skipn_all2 by (rewrite block_length; lia).
      cbn [app]; rewrite IH,N2Nat.inj_sub; reflexivity.
    + apply N.leb_gt in E; cbn [expand block_bits pat width len].
      replace (N.to_nat n-N.to_nat (len b))%nat with O by lia; cbn [skipn].
      unfold block_bits; cbn [pat width len]; rewrite bits_skipn by lia; rewrite rotate_spec by exact Hb.
      rewrite N2Nat.inj_sub; reflexivity.
Qed.
Lemma prefix_bound p w n: prefix p w n<2^N.of_nat n.
Proof.
  revert p; induction n; intro p; [change (0<1); lia|].
  cbn [prefix]; rewrite Nat2N.inj_succ,N.pow_succ_r'.
  specialize (IHn (rot1 w p)); destruct (N.odd p); cbn [N.b2n]; nia.
Qed.
Lemma prefix_good p w n: (1<=n<=8)%nat -> good (prefix p w n) n.
Proof.
  intro H; split; [exact H|].
  pose proof (prefix_bound p w n); unfold mask; rewrite N.shiftl_mul_pow2,N.mul_1_l; lia.
Qed.
Lemma code_app xs ys: code (xs++ys)=code xs+2^N.of_nat (List.length xs)*code ys.
Proof.
  induction xs as [|x xs IH]; [change (code ys=0+1*code ys); lia|].
  cbn [app code List.length]; rewrite IH,Nat2N.inj_succ,N.pow_succ_r'; nia.
Qed.
Definition append_check p w := forallb (fun v=>
  if Nat.leb (w+v) 8 then forallb (fun k=>let q:=N.of_nat k in
    let r:=N.lor p (N.shiftl q (N.of_nat w)) in
    andb (goodb r (w+v)) (N.eqb r (p+N.shiftl q (N.of_nat w))))
    (seq 0 (S (N.to_nat (mask v)))) else true) (seq 1 8).
Lemma append_checked: short_check append_check=true.
Proof. native_check_eq. Qed.
Lemma append_word p w q v: good p w -> good q v -> (w+v<=8)%nat ->
  let r:=N.lor p (N.shiftl q (N.of_nat w)) in good r (w+v) /\ r=p+N.shiftl q (N.of_nat w).
Proof.
  intros Hp [Hv Hq] Hsum; pose proof (short_check_spec _ append_checked p w Hp) as E.
  unfold append_check in E; rewrite forallb_forall in E.
  specialize (E v ltac:(apply in_seq; lia)).
  destruct (Nat.leb_spec0 (w+v) 8); [|lia].
  rewrite forallb_forall in E; specialize (E (N.to_nat q) ltac:(apply in_seq; lia)).
  rewrite N2Nat.id,Bool.andb_true_iff,goodb_spec,N.eqb_eq in E; exact E.
Qed.
Lemma short_append p w q v n m: (0<n)%nat -> (0<m)%nat -> (n+m<=8)%nat ->
  let r:=N.lor (prefix p w n) (N.shiftl (prefix q v m) (N.of_nat n)) in
  good r (n+m) /\ bits r (n+m) (n+m)=bits p w n++bits q v m.
Proof.
  intros Hn Hm Hsum; pose proof (append_word _ _ _ _
    (prefix_good p w n ltac:(lia)) (prefix_good q v m ltac:(lia)) Hsum) as [G E].
  split; [exact G|]; apply code_inj.
  - rewrite app_length,!bits_length; reflexivity.
  - rewrite code_app,!bits_code,bits_length,(proj2 (proj2 (word_facts _ _ G))).
    rewrite E,N.shiftl_mul_pow2; nia.
Qed.

Lemma merge_spec a b c: good_block a -> good_block b -> merge a b=Some c ->
  good_block c /\ block_bits c=block_bits a++block_bits b.
Proof.
  destruct a as [p w n],b as [q v m]; intros [Hp Hn] [Hq Hm].
  cbn [pat width len] in Hp,Hn,Hq,Hm; unfold merge; cbn [pat width len].
  destruct (andb (Nat.eqb w v) (N.eqb (rotate p w n) q)) eqn:E.
  - rewrite Bool.andb_true_iff,Nat.eqb_eq,N.eqb_eq in E; destruct E as [-> E].
    intros H; injection H as <-; split; [split; [exact Hp|cbn [len]; lia]|].
    unfold block_bits; cbn [pat width len]; rewrite bits_split by exact Hp; now rewrite E.
  - destruct (andb (N.leb n 8) (N.leb (N.of_nat v) m)) eqn:G; try discriminate.
    destruct (short_eq (rotate q v (N.of_nat v-n mod N.of_nat v)) v p w n) eqn:K; try discriminate.
    rewrite Bool.andb_true_iff,!N.leb_le in G; destruct G as [Gn Gm].
    destruct (back_spec _ _ _ Hq Gn) as [Gp Eq].
    unfold short_eq in K; apply N.eqb_eq in K; apply prefix_eq in K.
    intros H; injection H as <-; split; [split; [exact Gp|cbn [len]; lia]|].
    unfold block_bits; cbn [pat width len]; rewrite bits_split by exact Gp; now rewrite K,Eq.
Qed.
Lemma merge_more_spec a b c: good_block a -> good_block b -> merge_more a b=Some c ->
  good_block c /\ block_bits c=block_bits a++block_bits b.
Proof.
  intros Ha Hb; unfold merge_more; destruct (merge a b) as [x|] eqn:E.
  - intros H; injection H as <-; eapply merge_spec; eassumption.
  - destruct (andb (N.leb (len b) 8) (N.leb (N.of_nat (width a)) (len a))) eqn:G; try discriminate.
    destruct (short_eq (rotate (pat a) (width a) (len a)) (width a) (pat b) (width b) (len b)) eqn:K;
      try discriminate.
    unfold short_eq in K; apply N.eqb_eq in K; apply prefix_eq in K.
    intros H; injection H as <-; split.
    + split; [apply Ha|cbn [len]; destruct Ha,Hb; lia].
    + unfold block_bits; cbn [pat width len]; rewrite bits_split by apply Ha; now rewrite K.
Qed.
Lemma join_spec a b c: good_block a -> good_block b -> join a b=Some c ->
  good_block c /\ block_bits c=block_bits a++block_bits b.
Proof.
  intros Ha Hb; unfold join; destruct (merge_more a b) as [x|] eqn:E.
  - intros H; injection H as <-; eapply merge_more_spec; eassumption.
  - destruct (N.leb (len a+len b) 8) eqn:G; try discriminate; apply N.leb_le in G.
    destruct Ha as [Ha Hn],Hb as [Hb Hm].
    pose proof (short_append (pat a) (width a) (pat b) (width b)
      (N.to_nat (len a)) (N.to_nat (len b)) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hgood Hbits].
    rewrite N2Nat.id in Hgood,Hbits.
    intros H; injection H as <-; split.
    + split; cbn [pat width len]; [rewrite N2Nat.inj_add; exact Hgood|lia].
    + unfold block_bits; cbn [pat width len]; rewrite N2Nat.inj_add; exact Hbits.
Qed.
Lemma zero_side n: List.repeat S0 n *> 0inf=0inf.
Proof. induction n; [reflexivity|change (S0 >> (List.repeat S0 n *> 0inf)=0inf); rewrite IHn; symmetry; apply const_unfold]. Qed.
Lemma push_join_spec b s: good_block b -> valid s ->
  valid (push_join b s) /\ denote (push_join b s)=block_bits b *> denote s.
Proof.
  intros Hb Hs; revert b Hb; induction Hs as [|a s Ha Hs IH]; intros b Hb; cbn [push_join].
  - destruct (N.eqb (pat b) 0) eqn:E; split; try (constructor; auto; constructor).
    + apply N.eqb_eq in E; unfold denote,block_bits; cbn [expand]; rewrite E,bits_zero,zero_side; reflexivity.
    + unfold denote; cbn [expand]; rewrite app_nil_r; reflexivity.
  - destruct (join b a) as [c|] eqn:E.
    + destruct (join_spec _ _ _ Hb Ha E) as [Gc Ec].
      destruct (reduce_block _ Gc) as [Gr Er]; destruct (IH _ Gr) as [V D].
      split; [exact V|rewrite D,Er,Ec,Str_app_assoc,denote_cons; reflexivity].
    + split; [constructor; [exact Hb|constructor; assumption]|apply denote_cons].
Qed.
Lemma mask_checked: short_check (fun p w=>N.eqb (N.land p (mask w)) p)=true.
Proof. native_check_eq. Qed.
Lemma mask_id p w: good p w -> N.land p (mask w)=p.
Proof. intro H; apply N.eqb_eq; exact (short_check_spec _ mask_checked p w H). Qed.
Lemma push_spec p w n s: good p w -> valid s ->
  valid (push p w n s) /\ denote (push p w n s)=bits p w (N.to_nat n) *> denote s.
Proof.
  intros Hp Hs; unfold push; destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; split; [exact Hs|reflexivity].
  - apply N.eqb_neq in E; rewrite mask_id by exact Hp.
    assert (Gb: good_block (Bl p w n)) by (split; cbn [pat width len]; auto; lia).
    destruct (reduce_block _ Gb) as [Gr Er]; destruct (push_join_spec _ _ Gr Hs) as [V D].
    split; [exact V|rewrite D,Er; reflexivity].
Qed.
Lemma digit_sym b: digit (sym b)=N.b2n b.
Proof. destruct b; reflexivity. Qed.
Lemma sym_digit b: sym (N.odd (digit b))=b.
Proof. destruct b; reflexivity. Qed.
Lemma top_spec s: valid s -> top s=digit (Streams.hd (denote s)).
Proof.
  intros H; destruct H as [|[p w n] s [G Hn] Hs]; [reflexivity|].
  cbn [len] in Hn; unfold denote; cbn [expand block_bits pat width len top].
  unfold block_bits; cbn [pat width len].
  destruct (N.to_nat n) eqn:E; [lia|].
  cbn [bits app Str_app Streams.hd]; apply eq_sym,digit_sym.
Qed.
Fixpoint take_side n (r:side) := match n with
  | O=>[] | S n=>Streams.hd r::take_side n (Streams.tl r) end.
Fixpoint skip_side n (r:side) := match n with
  | O=>r | S n=>skip_side n (Streams.tl r) end.
Lemma skip_side_zero n: skip_side n 0inf=0inf.
Proof. induction n; [reflexivity|change (skip_side n 0inf=0inf); assumption]. Qed.
Lemma skip_side_list n xs: skip_side n (xs *> 0inf)=skipn n xs *> 0inf.
Proof.
  revert xs; induction n; intros [|x xs]; cbn [skip_side skipn]; try reflexivity.
  - change (skip_side n 0inf=0inf); apply skip_side_zero.
  - apply IHn.
Qed.
Lemma drop_spec s n: valid s -> denote (drop n s)=skip_side (N.to_nat n) (denote s).
Proof. intro H; unfold denote; rewrite drop_expand by exact H; symmetry; apply skip_side_list. Qed.
Lemma take_skip n r: r=take_side n r *> skip_side n r.
Proof.
  revert r; induction n; intro r; [reflexivity|].
  cbn [take_side skip_side Str_app]; rewrite <-IHn; apply Cons_unfold.
Qed.
Lemma pop_spec s: valid s -> denote (drop 1 s)=Streams.tl (denote s).
Proof. intro H; rewrite drop_spec by exact H; reflexivity. Qed.
Lemma peek_spec n s: valid s -> peek n s=code (take_side n (denote s)).
Proof.
  revert s; induction n; intros s Hs; [reflexivity|].
  cbn [peek take_side code]; rewrite top_spec,IHn by assumption || apply drop_valid,Hs.
  rewrite pop_spec by exact Hs; reflexivity.
Qed.
Lemma push_digit b s: valid s ->
  valid (push1 (digit b) s) /\ denote (push1 (digit b) s)=b >> denote s.
Proof.
  intro H; assert (G: good (digit b) 1) by
    (destruct b; split; cbn [digit]; try lia; vm_compute; discriminate).
  destruct (push_spec _ _ 1 s G H) as [V E]; split; [exact V|].
  unfold push1; rewrite E; change (sym (N.odd (digit b)) >> denote s=b >> denote s).
  rewrite sym_digit; reflexivity.
Qed.
Lemma read_top s: valid s ->
  (if N.eqb (top s) 0 then S0 else S1)=Streams.hd (denote s).
Proof. intro H; rewrite top_spec by exact H; destruct (Streams.hd (denote s)); reflexivity. Qed.
Lemma push_top x s: valid x -> valid s ->
  valid (push1 (top x) s) /\ denote (push1 (top x) s)=Streams.hd (denote x) >> denote s.
Proof. intros Hx Hs; rewrite top_spec by exact Hx; apply push_digit,Hs. Qed.
Definition config (s:state) := let '(q,l,r):=s in denote l {{q}}> denote r.
Definition valid_state (s:state) := let '(_,l,r):=s in valid l /\ valid r.
Lemma primitive_spec tm s t: valid_state s -> primitive tm s=Some t ->
  valid_state t /\ step_c tm (config s)=Some (config t).
Proof.
  destruct s as [[q l] r]; intros [Hl Hr]; unfold primitive; rewrite read_top by exact Hr.
  match goal with |- context[tm ?x]=>destruct (tm x) as [[[b d] q']|] eqn:E end; try discriminate.
  destruct d; intros H; injection H as <-.
  - destruct (push_digit b _ (drop_valid r 1 Hr)) as [Vr Er].
    destruct (push_top l _ Hl Vr) as [Vr' Er'].
    split; [split; [apply drop_valid,Hl|exact Vr']|].
    unfold config; fold (digit b); rewrite Er',Er,!pop_spec by assumption.
    cbn [step_c move_left Streams.hd Streams.tl]; fold Q Sym in E; rewrite E; reflexivity.
  - destruct (push_digit b l Hl) as [Vl El].
    split; [split; [exact Vl|apply drop_valid,Hr]|].
    unfold config; fold (digit b); rewrite El,pop_spec by exact Hr.
    cbn [step_c move_right Streams.hd Streams.tl]; fold Q Sym in E; rewrite E; reflexivity.
Qed.
Lemma primitive_halt tm s: valid_state s -> primitive tm s=None -> halts tm (config s).
Proof.
  destruct s as [[q l] r]; intros [Hl Hr]; unfold primitive; rewrite read_top by exact Hr.
  match goal with |- context[tm ?x]=>destruct (tm x) as [[[b d] q']|] eqn:E end;
    [destruct d; discriminate|].
  intros _; apply halted_halts; exact E.
Qed.
End PeriodicTape.

(* The bounded scan may stop early, but every returned repetition matches. *)
Import ListNotations PeriodicRuntime PeriodicTape.
Open Scope N_scope.

Module PeriodicScan.
Lemma common_period p w q v: good p w -> good q v ->
  prefix p w (Nat.lcm w v)=prefix q v (Nat.lcm w v) -> forall n, bits p w n=bits q v n.
Proof.
  intros Hp Hq E; apply same_period with (d:=Nat.lcm w v).
  - assert (H: Nat.lcm w v<>O).
    { intro H; apply Nat.lcm_eq_0 in H; destruct Hp,Hq; lia. } lia.
  - destruct (Nat.divide_lcm_l w v) as [k ->]; apply rotate_multiple,word_facts,Hp.
  - destruct (Nat.divide_lcm_r w v) as [k ->]; apply rotate_multiple,word_facts,Hq.
  - apply prefix_eq,E.
Qed.
Lemma rotate_words p w n: good p w -> rotate_small p w (N.to_nat (n*N.of_nat w))=p.
Proof. intro H; rewrite N2Nat.inj_mul,Nat2N.id; apply rotate_multiple,word_facts,H. Qed.
Lemma bits_words p w n: good p w -> bits p w (n*w)=bits p w w^^n.
Proof.
  intro H; induction n; [reflexivity|].
  cbn [Nat.mul]; rewrite bits_add,(proj1 (proj2 (word_facts _ _ H))),IHn; reflexivity.
Qed.
Lemma take_side_length n r: List.length (take_side n r)=n.
Proof. revert r; induction n; intros; cbn [take_side List.length]; auto. Qed.
Lemma take_side_add n m r:
  take_side (n+m) r=take_side n r++take_side m (skip_side n r).
Proof.
  revert r; induction n; intros; cbn [Nat.add take_side skip_side]; rewrite ?IHn; reflexivity.
Qed.
Lemma take_side_prefix n xs r: (n<=List.length xs)%nat -> take_side n (xs *> r)=firstn n xs.
Proof.
  revert xs r; induction n; intros [|x xs] r H; cbn [List.length] in H; try lia;
    cbn [take_side firstn Str_app Streams.hd Streams.tl]; try reflexivity; f_equal; apply IHn; lia.
Qed.
Definition matches p w n s :=
  take_side (N.to_nat (n*N.of_nat w)) (denote s)=bits p w (N.to_nat (n*N.of_nat w)).
Lemma matches_zero p w s: matches p w 0 s.
Proof. reflexivity. Qed.
Lemma matches_one p w s: good p w -> valid s -> peek w s=p -> matches p w 1 s.
Proof.
  intros Hp Hs Hpeek; unfold matches; rewrite N.mul_1_l,Nat2N.id.
  apply code_inj; [rewrite take_side_length,bits_length; reflexivity|].
  rewrite <-peek_spec by exact Hs; rewrite bits_code,Hpeek; symmetry; apply word_facts,Hp.
Qed.
Lemma matches_compose p w n m s: good p w -> valid s ->
  matches p w n s -> matches p w m (drop (n*N.of_nat w) s) -> matches p w (n+m) s.
Proof.
  intros Hp Hs Hn Hm; unfold matches in *.
  rewrite N.mul_add_distr_r,N2Nat.inj_add,take_side_add,bits_add,rotate_words by exact Hp.
  rewrite <-drop_spec by exact Hs; now rewrite Hn,Hm.
Qed.
Lemma matches_decompose p w n s: good p w -> valid s -> matches p w n s ->
  denote s=bits p w w^^(N.to_nat n) *> denote (drop (n*N.of_nat w) s).
Proof.
  intros Hp Hs H; rewrite (take_skip (N.to_nat (n*N.of_nat w)) (denote s)).
  rewrite H,<-drop_spec by exact Hs; rewrite N2Nat.inj_mul,Nat2N.id,bits_words by exact Hp; reflexivity.
Qed.

Definition bulk p w limit s := match s with
  | []=>0 | b::_=>let per:=Nat.lcm w (width b) in
    if andb (N.leb (N.of_nat per) (len b))
      (N.eqb (prefix (pat b) (width b) per) (prefix p w per))
    then N.min limit (len b/N.of_nat w) else 0 end.
Lemma bulk_spec p w limit s: good p w -> valid s ->
  bulk p w limit s<=limit /\ matches p w (bulk p w limit s) s.
Proof.
  intros Hp Hs; destruct Hs as [|b s [Hb Hlen] Hs]; [cbn [bulk]; split; [lia|apply matches_zero]|].
  unfold bulk; destruct (andb (N.leb (N.of_nat (Nat.lcm w (width b))) (len b))
    (N.eqb (prefix (pat b) (width b) (Nat.lcm w (width b))) (prefix p w (Nat.lcm w (width b))))) eqn:E.
  - split; [apply N.le_min_l|].
    rewrite Bool.andb_true_iff,N.leb_le,N.eqb_eq in E; destruct E as [Hper E].
    assert (Hfit: N.min limit (len b/N.of_nat w)*N.of_nat w<=len b).
    { pose proof (N.le_min_r limit (len b/N.of_nat w)).
      pose proof (N.div_mod (len b) (N.of_nat w) ltac:(destruct Hp; lia)); nia. }
    unfold matches; rewrite denote_cons,take_side_prefix by (rewrite block_length; lia).
    unfold block_bits; rewrite bits_firstn by lia.
    symmetry; apply common_period; try assumption; symmetry; exact E.
  - split; [lia|apply matches_zero].
Qed.
Lemma count_rec_spec fuel p w limit s: good p w -> valid s ->
  count_rec fuel p w limit s<=limit /\ matches p w (count_rec fuel p w limit s) s.
Proof.
  revert limit s; induction fuel as [|fuel IH]; intros limit s Hp Hs.
  - cbn [count_rec]; split; [lia|apply matches_zero].
  - cbn [count_rec]; fold (bulk p w limit s); destruct (N.eqb limit 0) eqn:Hz.
    + split; [lia|apply matches_zero].
    + apply N.eqb_neq in Hz; destruct (N.eqb (bulk p w limit s) 0) eqn:Hb.
      * destruct (N.eqb (peek w s) p) eqn:E; [|split; [lia|apply matches_zero]].
        apply N.eqb_eq in E.
        destruct (IH (limit-1) (drop (N.of_nat w) s) Hp (drop_valid _ _ Hs)) as [Hbound Hmatch].
        split; [lia|apply matches_compose; try assumption; [apply matches_one; assumption|]].
        rewrite N.mul_1_l; exact Hmatch.
      * destruct (bulk_spec _ _ limit _ Hp Hs) as [Hbulk Hmatched].
        destruct (IH (limit-bulk p w limit s) (drop (bulk p w limit s*N.of_nat w) s)
          Hp (drop_valid _ _ Hs)) as [Hbound Hmatch].
        split; [lia|apply matches_compose; assumption].
Qed.
Lemma count_spec p w s: good p w -> valid s ->
  denote s=bits p w w^^(N.to_nat (count p w s)) *> denote (drop (count p w s*N.of_nat w) s).
Proof.
  intros Hp Hs; apply matches_decompose; try assumption.
  apply count_rec_spec; assumption.
Qed.
Lemma push_words p w n s: good p w -> valid s ->
  valid (push p w (n*N.of_nat w) s) /\
  denote (push p w (n*N.of_nat w) s)=bits p w w^^(N.to_nat n) *> denote s.
Proof.
  intros Hp Hs; destruct (push_spec p w (n*N.of_nat w) s Hp Hs) as [V E].
  split; [exact V|rewrite E,N2Nat.inj_mul,Nat2N.id,bits_words by exact Hp; reflexivity].
Qed.
Lemma left_state_spec q l r: valid l -> valid r ->
  valid_state (q,drop 1 l,push1 (top l) r) /\
  config (q,drop 1 l,push1 (top l) r)=denote l <{{q}} denote r.
Proof.
  intros Hl Hr; destruct (push_top l r Hl Hr) as [V E].
  split; [split; [apply drop_valid,Hl|exact V]|].
  unfold config; rewrite E,pop_spec by exact Hl; reflexivity.
Qed.
Lemma turn_state q l r: valid l -> valid r ->
  config (q,l,r)=denote (push1 (top r) l) <{{q}} denote (drop 1 r).
Proof.
  intros Hl Hr; destruct (push_top r l Hr Hl) as [_ E].
  unfold config; rewrite E,pop_spec by exact Hr; reflexivity.
Qed.
Definition shift_valid (tm:TM) h := good (sin h) (sw h) /\ good (sout h) (sw h) /\
  forall n l r, match sd h with
  | R=>l {{sq h}}> bits (sin h) (sw h) (sw h)^^n *> r -[tm]->*
       l <* bits (sout h) (sw h) (sw h)^^n {{sq h}}> r
  | L=>l <* bits (sin h) (sw h) (sw h)^^n <{{sq h}} r -[tm]->*
       l <{{sq h}} bits (sout h) (sw h) (sw h)^^n *> r end.
Lemma try_shift_spec tm h s t: shift_valid tm h -> valid_state s -> try_shift h s=Some t ->
  valid_state t /\ config s -[tm]->* config t.
Proof.
  destruct h as [q d w p v],s as [[q' l] r]; intros [Hp [Hv Hshift]] [Hl Hr].
  unfold try_shift; cbn [sq sd sw sin sout] in *.
  destruct (q_eqb_spec q' q); try discriminate; subst q'; destruct d.
  - set (x:=push1 (top r) l); set (n:=count p w x).
    destruct (N.ltb 1 n); try discriminate; intros H; injection H as <-.
    destruct (push_top r l Hr Hl) as [Hx Ex].
    change (valid x) in Hx.
    destruct (push_words v w n (drop 1 r) Hv (drop_valid r 1 Hr)) as [Vr Er].
    destruct (left_state_spec q (drop (n*N.of_nat w) x) _ (drop_valid _ _ Hx) Vr) as [V E].
    split; [exact V|].
    eapply evstep_trans; [apply evstep_refl'; exact (turn_state q l r Hl Hr)|].
    rewrite Er in E; eapply evstep_trans; [|apply evstep_refl'; symmetry; exact E].
    change (denote x <{{q}} denote (drop 1 r) -[tm]->*
      denote (drop (n*N.of_nat w) x) <{{q}} bits v w w^^(N.to_nat n) *> denote (drop 1 r)).
    rewrite (count_spec p w x Hp Hx); apply Hshift.
  - set (n:=count p w r); destruct (N.ltb 1 n); try discriminate; intros H; injection H as <-.
    destruct (push_words v w n l Hv Hl) as [Vl El].
    split; [split; [exact Vl|apply drop_valid,Hr]|].
    unfold config; rewrite El,(count_spec p w r Hp Hr); apply Hshift.
Qed.
Lemma scan_spec tm hs s t: Forall (shift_valid tm) hs -> valid_state s -> scan hs s=Some t ->
  valid_state t /\ config s -[tm]->* config t.
Proof.
  intros H; induction H; intros Hs; cbn [scan]; [discriminate|].
  destruct (try_shift x s) as [u|] eqn:E.
  - intros G; injection G as <-; eapply try_shift_spec; eassumption.
  - apply IHForall,Hs.
Qed.
End PeriodicScan.

(* Arithmetic semantics of the compressed binary counters. *)
Import ListNotations PeriodicRuntime PeriodicTape.
Open Scope N_scope.

Module PeriodicCounter.
Definition part_ok (x:part) := fst x<4 /\ 0<snd x.
Definition parts_ok := Forall part_ok.
Definition word p n := bits p 2 (N.to_nat n).
Fixpoint digits xs := match xs with []=>[] | (p,n)::xs=>word p n++digits xs end.
Definition rdigits xs := digits (rev xs).
Definition scale n : Z := 2^Z.of_N n.
Definition zcode xs := Z.of_N (code xs).
Definition value xs := zcode (digits xs).
Definition rvalue xs := zcode (rdigits xs).
Definition val p n := zcode (word p n).

Lemma good_two p: p<4 -> good p 2.
Proof. intro H; split; [lia|change (p<=3); lia]. Qed.
Lemma rot2_spec p n: p<4 -> rot2 p n=rotate p 2 n.
Proof.
  intro H; unfold rotate; rewrite <-N.bit0_mod,N.bit0_odd.
  unfold rot2; destruct (N.odd n); cbn [N.b2n N.to_nat rotate_small].
  - change (N.div2 p+2*N.b2n (N.odd p)=rot1 2 p).
    unfold rot1; destruct (N.odd p); reflexivity.
  - reflexivity.
Qed.
Lemma rot2_bound p n: p<4 -> rot2 p n<4.
Proof.
  intro H; rewrite rot2_spec by exact H.
  pose proof (rotate_good p 2 n (good_two p H)) as [_ E]; change (rotate p 2 n<=3) in E; lia.
Qed.
Lemma rot2_twice p: p<4 -> rot2 (rot2 p 1) 1=p.
Proof. intro H; assert (p=0 \/ p=1 \/ p=2 \/ p=3) by lia; intuition subst; reflexivity. Qed.
Lemma word_split p n m: p<4 -> word p (n+m)=word p n++word (rot2 p n) m.
Proof. intro H; unfold word; rewrite bits_split,rot2_spec by (auto using good_two); reflexivity. Qed.
Lemma word_one p q: N.odd p=N.odd q -> word p 1=word q 1.
Proof. intro H; change ([sym (N.odd p)]=[sym (N.odd q)]); now rewrite H. Qed.
Lemma word_length p n: List.length (word p n)=N.to_nat n.
Proof. apply bits_length. Qed.
Lemma digits_app xs ys: digits (xs++ys)=digits xs++digits ys.
Proof. induction xs as [|[p n] xs IH]; cbn [app digits]; rewrite ?IH,?app_assoc; reflexivity. Qed.
Lemma digits_length xs: List.length (digits xs)=N.to_nat (bsize xs).
Proof. induction xs as [|[p n] xs IH]; cbn [digits bsize]; rewrite ?app_length,?word_length,?IH,?N2Nat.inj_add; reflexivity. Qed.
Lemma bsize_app xs ys: bsize (xs++ys)=bsize xs+bsize ys.
Proof. induction xs as [|[p n] xs IH]; cbn [bsize app]; rewrite ?IH; lia. Qed.
Lemma bsize_rev xs: bsize (rev xs)=bsize xs.
Proof. induction xs as [|[p n] xs IH]; cbn [rev bsize]; rewrite ?bsize_app,?IH; cbn [bsize]; lia. Qed.
Lemma rdigits_cons p n xs: rdigits ((p,n)::xs)=rdigits xs++word p n.
Proof. unfold rdigits; cbn [rev]; rewrite digits_app; cbn [digits]; now rewrite app_nil_r. Qed.
Lemma samepart_spec p q n: samepart p q n=true -> word p n=word q n.
Proof.
  unfold samepart; destruct (N.eqb_spec n 1); [subst; intro H; apply word_one,Bool.eqb_prop,H|].
  intro H; apply N.eqb_eq in H; now subst.
Qed.
Lemma normalize_part p n:
  p<4 -> let q:=if N.eqb n 1 then if N.odd p then 3 else 0 else p in
  q<4 /\ word q n=word p n.
Proof.
  intro H; destruct (N.eqb_spec n 1); [subst; destruct (N.odd p) eqn:E|];
    split; try lia; try reflexivity; apply word_one; cbn; symmetry; exact E.
Qed.
Lemma add_part_spec p n acc: p<4 -> parts_ok acc ->
  parts_ok (add_part p n acc) /\ rdigits (add_part p n acc)=rdigits acc++word p n.
Proof.
  intros Hp Hacc; unfold add_part; destruct (N.eqb_spec n 0).
  - subst; split; [exact Hacc|unfold word; cbn [N.to_nat bits]; now rewrite app_nil_r].
  - destruct (normalize_part p n Hp) as [Hq Eq].
    set (q:=if N.eqb n 1 then if N.odd p then 3 else 0 else p) in *.
    rewrite <-Eq; destruct Hacc as [|[a k] acc [Ha Hk] Hacc].
    + split; [constructor; [split; cbn; lia|constructor]|].
      unfold rdigits; cbn [rev digits]; apply app_nil_r.
    + cbn [fst snd] in Ha,Hk; destruct (samepart (rot2 a k) q n) eqn:E.
      * split; [constructor; [split; cbn; lia|exact Hacc]|].
        rewrite !rdigits_cons,word_split by exact Ha.
        rewrite (samepart_spec _ _ _ E),app_assoc; reflexivity.
      * destruct (N.eqb_spec k 1).
        -- subst k; destruct (Bool.eqb (N.odd (rot2 q 1)) (N.odd a)) eqn:F.
           ++ split; [constructor; [split; [exact (rot2_bound q 1 Hq)|cbn; lia]|exact Hacc]|].
              rewrite !rdigits_cons,N.add_comm,word_split by (apply rot2_bound,Hq).
              rewrite rot2_twice by exact Hq.
              rewrite (word_one _ _ (Bool.eqb_prop _ _ F)),app_assoc; reflexivity.
           ++ destruct (N.eqb_spec n 1).
              ** subst n; split; [constructor; [split; cbn; [destruct (N.odd a),(N.odd q); cbn; lia|lia]|exact Hacc]|].
                 rewrite !rdigits_cons,<-app_assoc; f_equal.
                 change (bits (N.b2n (N.odd a)+2*N.b2n (N.odd q)) 2 2=
                   [sym (N.odd a);sym (N.odd q)]).
                 destruct (N.odd a),(N.odd q); reflexivity.
              ** split; [constructor; [split; cbn; lia|constructor; [split; cbn; lia|exact Hacc]]|apply rdigits_cons].
        -- split; [constructor; [split; cbn; lia|constructor; [split; cbn; lia|exact Hacc]]|apply rdigits_cons].
Qed.
Lemma add_part_size p n acc: p<4 -> parts_ok acc -> bsize (add_part p n acc)=bsize acc+n.
Proof.
  intros Hp Hacc; apply N2Nat.inj.
  pose proof (f_equal (@List.length _) (proj2 (add_part_spec p n acc Hp Hacc))) as E.
  unfold rdigits in E; rewrite app_length,!digits_length,!bsize_rev,word_length in E.
  now rewrite N2Nat.inj_add.
Qed.
Lemma scale_add n m: scale (n+m)=(scale n*scale m)%Z.
Proof. unfold scale; rewrite N2Z.inj_add,Z.pow_add_r by lia; reflexivity. Qed.
Lemma scale_pos n: (0<scale n)%Z.
Proof. unfold scale; apply Z.pow_pos_nonneg; lia. Qed.
Lemma zcode_app xs ys:
  zcode (xs++ys)=(zcode xs+scale (N.of_nat (List.length xs))*zcode ys)%Z.
Proof. unfold zcode,scale; rewrite code_app,N2Z.inj_add,N2Z.inj_mul,N2Z.inj_pow; reflexivity. Qed.
Lemma rvalue_cons p n xs: rvalue ((p,n)::xs)=(rvalue xs+scale (bsize xs)*val p n)%Z.
Proof.
  unfold rvalue,val; rewrite rdigits_cons,zcode_app; unfold rdigits.
  rewrite digits_length,bsize_rev,N2Nat.id; reflexivity.
Qed.
Lemma add_part_value p n acc: p<4 -> parts_ok acc ->
  rvalue (add_part p n acc)=(rvalue acc+scale (bsize acc)*val p n)%Z.
Proof.
  intros Hp Hacc; unfold rvalue,val; rewrite (proj2 (add_part_spec p n acc Hp Hacc)),zcode_app.
  unfold rdigits; rewrite digits_length,bsize_rev,N2Nat.id; reflexivity.
Qed.
Lemma val_split p n m: p<4 -> val p (n+m)=(val p n+scale n*val (rot2 p n) m)%Z.
Proof.
  intro H; unfold val; rewrite word_split,zcode_app by exact H.
  rewrite word_length,N2Nat.id; reflexivity.
Qed.
Lemma val_zero n: val 0 n=0%Z.
Proof.
  unfold val,word,zcode; rewrite bits_zero.
  induction (N.to_nat n); [reflexivity|].
  cbn [List.repeat code digit] in *; lia.
Qed.
Lemma val_nil p: val p 0=0%Z.
Proof. reflexivity. Qed.
Lemma val_one p: val p 1=Periodic2.bit (N.odd p).
Proof. change (Z.of_N (code [sym (N.odd p)])=Periodic2.bit (N.odd p)); destruct (N.odd p); reflexivity. Qed.
Lemma val_bounds p n: (0<=val p n<scale n)%Z.
Proof.
  pose proof (prefix_bound p 2 (N.to_nat n)) as H; rewrite N2Nat.id in H.
  pose proof (N2Z.inj_pow 2 n) as E; change (Z.of_N (2^n)=scale n) in E.
  unfold val,word,zcode; rewrite bits_code; lia.
Qed.
Lemma val_drop_zero p n: p<4 -> 0<n -> N.odd (rot2 p (n-1))=false -> val p n=val p (n-1).
Proof.
  intros Hp Hn E; replace n with (n-1+1) at 1 by lia.
  rewrite val_split,val_one,E by exact Hp; cbn [Periodic2.bit]; ring.
Qed.
Lemma trim_rev_spec xs: parts_ok xs -> parts_ok (trim_rev xs) /\
  bsize (trim_rev xs)<=bsize xs /\ rvalue (trim_rev xs)=rvalue xs.
Proof.
  intro H; induction H as [|[p n] xs [Hp Hn] Hxs [V [Hs He]]].
  - repeat split; try constructor; reflexivity.
  - cbn [fst snd] in Hp,Hn; cbn [trim_rev].
    destruct (N.eqb_spec p 0).
    + subst p; split; [exact V|split; [cbn [bsize]; lia|]].
      rewrite rvalue_cons,val_zero,He; ring.
    + destruct (N.odd (rot2 p (n-1))) eqn:E.
      * split; [constructor; [split; assumption|exact Hxs]|split; reflexivity].
      * pose proof (val_drop_zero p n Hp Hn E) as Ev; destruct (N.eqb_spec n 1).
        -- subst n; change (val p 1=0%Z) in Ev.
           split; [exact Hxs|split; [cbn [bsize]; lia|rewrite rvalue_cons,Ev; ring]].
        -- split; [constructor; [split; cbn; lia|exact Hxs]|split; [cbn [bsize]; lia|]].
           rewrite !rvalue_cons,Ev; reflexivity.
Qed.
Lemma zcode_cons b xs: zcode (sym b::xs)=(Periodic2.bit b+2*zcode xs)%Z.
Proof. unfold zcode; cbn [code]; rewrite N2Z.inj_add,N2Z.inj_mul; destruct b; reflexivity. Qed.
Lemma pair_rot p: p<4 -> to_pair (rot1 2 p)=Periodic2.swap (to_pair p).
Proof. intro H; assert (p=0 \/ p=1 \/ p=2 \/ p=3) by lia; intuition subst; reflexivity. Qed.
Lemma val_alt p n: p<4 -> val p n=Periodic2.alt (to_pair p) (N.to_nat n).
Proof.
  unfold val,word; generalize (N.to_nat n) as k; intros k; revert p.
  induction k as [|k IH]; intros p Hp; [reflexivity|].
  cbn [bits Periodic2.alt]; rewrite zcode_cons,IH.
  - rewrite pair_rot by exact Hp; reflexivity.
  - pose proof (proj1 (word_facts p 2 (good_two p Hp))) as [_ H]; change (rot1 2 p<=3) in H; lia.
Qed.
Lemma val_even p k: p<4 -> val p (k+k)=Periodic2.tile (to_pair p) (N.to_nat k).
Proof. intro H; rewrite val_alt,N2Nat.inj_add,Periodic2.alt_even by exact H; reflexivity. Qed.
Lemma scale_even k: scale (k+k)=Periodic2.radix (N.to_nat k).
Proof.
  pattern k; apply N.peano_ind; [reflexivity|].
  intros n H; replace (N.succ n+N.succ n) with (2+(n+n)) by lia.
  rewrite scale_add,H,N2Nat.inj_succ; reflexivity.
Qed.
Lemma minus_pair_spec p q c: p<4 -> q<4 ->
  let '(v,d):=minus_pair p q c in v<4 /\
    (val p 2-val q 2-Periodic2.bit c=val v 2-4*Periodic2.bit d)%Z.
Proof.
  intros Hp Hq; assert (P: p=0 \/ p=1 \/ p=2 \/ p=3) by lia;
    assert (Q: q=0 \/ q=1 \/ q=2 \/ q=3) by lia.
  destruct P as [-> | [-> | [-> | ->]]]; destruct Q as [-> | [-> | [-> | ->]]];
    destruct c; cbn; split; reflexivity.
Qed.
Lemma minus_bit_spec p q c: let '(v,d):=minus_bit p q c in v<4 /\
  (val p 1-val q 1-Periodic2.bit c=val v 1-2*Periodic2.bit d)%Z.
Proof.
  unfold minus_bit; rewrite !val_one; destruct (N.odd p),(N.odd q),c; cbn;
    split; reflexivity.
Qed.
Lemma minus_stable p q c:
  snd (minus_pair p q (snd (minus_pair p q c)))=snd (minus_pair p q c).
Proof.
  unfold minus_pair; pose proof (Periodic2.borrow_stable (to_pair p) (to_pair q) c) as E.
  destruct (Periodic2.subpair (to_pair p) (to_pair q) c) as [v d]; cbn [snd] in *.
  destruct (Periodic2.subpair (to_pair p) (to_pair q) d); exact E.
Qed.
Lemma minus_repeated p q c v k: p<4 -> q<4 -> minus_pair p q c=(v,c) ->
  (val p (k+k)-val q (k+k)-Periodic2.bit c=val v (k+k)-scale (k+k)*Periodic2.bit c)%Z.
Proof.
  intros Hp Hq E; unfold minus_pair in E.
  destruct (Periodic2.subpair (to_pair p) (to_pair q) c) as [[lo hi] d] eqn:H.
  injection E as <- <-; rewrite !val_even,scale_even by
    (try assumption; unfold from_pair; destruct lo,hi; cbn; lia).
  replace (to_pair (from_pair (lo,hi))) with (lo,hi) by (destruct lo,hi; reflexivity).
  apply Periodic2.tile_stable,H.
Qed.
Lemma rot2_even p k: rot2 p (k+k)=p.
Proof. unfold rot2; rewrite N.odd_add; destruct (N.odd k); reflexivity. Qed.
Lemma subtract_part_spec p q c n acc out d:
  p<4 -> q<4 -> 0<n -> parts_ok acc -> subtract_part p q c n acc=(out,d) ->
  parts_ok out /\ bsize out=bsize acc+n /\
  rvalue out=(rvalue acc+scale (bsize acc)*
    (val p n-val q n-Periodic2.bit c+scale n*Periodic2.bit d))%Z.
Proof.
  intros Hp Hq Hn Hacc; unfold subtract_part; destruct (N.eqb_spec n 1).
  - subst n; pose proof (minus_bit_spec p q c) as E.
    destruct (minus_bit p q c) as [v e]; destruct E as [Hv Ev].
    intros H; injection H as <- <-; split; [apply add_part_spec; assumption|].
    split; [apply add_part_size; assumption|rewrite add_part_value by assumption].
    change (scale 1) with 2%Z; nia.
  - pose proof (minus_pair_spec p q c Hp Hq) as E1.
    pose proof (minus_stable p q c) as Es.
    destruct (minus_pair p q c) as [v e] eqn:Hv; cbn [snd] in Es.
    destruct E1 as [Vv E1].
    pose proof (minus_pair_spec p q e Hp Hq) as E2.
    destruct (minus_pair p q e) as [u e'] eqn:Hu; cbn [snd] in Es; subst e'.
    destruct E2 as [Vu E2].
    set (k:=N.div2 (n-2)).
    assert (D: N.double k=k+k) by (rewrite N.double_spec; lia).
    rewrite D; set (acc1:=add_part v 2 acc); set (acc2:=add_part u (k+k) acc1).
    assert (V1: parts_ok acc1) by (apply add_part_spec; assumption).
    assert (V2: parts_ok acc2) by (apply add_part_spec; assumption).
    assert (S1: bsize acc1=bsize acc+2) by (apply add_part_size; assumption).
    assert (S2: bsize acc2=bsize acc+2+(k+k)) by
      (unfold acc2; rewrite add_part_size by assumption; lia).
    pose proof (minus_repeated p q e u k Hp Hq Hu) as Eb.
    assert (V2eq: rvalue acc2=(rvalue acc+scale (bsize acc)*
      (val p (2+(k+k))-val q (2+(k+k))-Periodic2.bit c+
       scale (2+(k+k))*Periodic2.bit e))%Z).
    { unfold acc2; rewrite add_part_value by assumption.
      unfold acc1; rewrite add_part_value,add_part_size by assumption.
      rewrite (val_split p 2 (k+k) Hp),(val_split q 2 (k+k) Hq).
      change (rot2 p 2) with p; change (rot2 q 2) with q.
      rewrite (scale_add (bsize acc) 2),(scale_add 2 (k+k)); change (scale 2) with 4%Z; nia. }
    pose proof (N.div2_odd (n-2)) as Hsplit; fold k in Hsplit.
    destruct (N.odd (n-2)) eqn:Hodd; cbn [N.b2n] in Hsplit.
    + pose proof (minus_bit_spec p q e) as E3.
      destruct (minus_bit p q e) as [w f]; destruct E3 as [Vw E3].
      intros H; injection H as <- <-; split; [apply add_part_spec; assumption|].
      split; [rewrite add_part_size by assumption; lia|].
      rewrite add_part_value by assumption; rewrite V2eq,S2.
      assert (En: n=(2+(k+k))+1) by lia; rewrite En.
      rewrite (val_split p (2+(k+k)) 1 Hp),(val_split q (2+(k+k)) 1 Hq).
      replace (2+(k+k)) with ((1+k)+(1+k)) by lia.
      rewrite !rot2_even,!scale_add; change (scale 1) with 2%Z; change (scale 2) with 4%Z.
      assert (W: val w 1=(val p 1-val q 1-Periodic2.bit e+2*Periodic2.bit f)%Z) by lia.
      rewrite W; ring.
    + intros H; injection H as <- <-; split; [exact V2|split; [lia|]].
      replace n with (2+(k+k)) by lia; exact V2eq.
Qed.

Lemma value_cons p n xs: value ((p,n)::xs)=(val p n+scale n*value xs)%Z.
Proof. unfold value; cbn [digits]; rewrite zcode_app,word_length,N2Nat.id; reflexivity. Qed.
Lemma cut_low_spec p k n xs: p<4 -> 0<n<=k -> parts_ok xs ->
  parts_ok (cut_low p k n xs) /\ bsize (cut_low p k n xs)=k-n+bsize xs /\
  value ((p,k)::xs)=(val p n+scale n*value (cut_low p k n xs))%Z.
Proof.
  intros Hp Hn Hxs; unfold cut_low; destruct (N.eqb_spec k n).
  - subst k; split; [exact Hxs|split; [lia|apply value_cons]].
  - split; [constructor; [split; [apply rot2_bound,Hp|cbn; lia]|exact Hxs]|].
    split; [reflexivity|rewrite !value_cons].
    replace k with (n+(k-n)) at 1 by lia.
    rewrite val_split by exact Hp.
    assert (E: scale k=(scale n*scale (k-n))%Z) by
      (rewrite <-scale_add; f_equal; lia).
    rewrite E; ring.
Qed.
Lemma subtract_rec_spec fuel xs ys c acc out:
  parts_ok xs -> parts_ok ys -> parts_ok acc -> subtract_rec fuel xs ys c acc=Some out ->
  parts_ok out /\ bsize out=bsize acc+bsize xs /\
  rvalue out=(rvalue acc+scale (bsize acc)*(value xs-value ys-Periodic2.bit c))%Z.
Proof.
  revert xs ys c acc out; induction fuel as [|fuel IH]; intros xs ys c acc out Hx Hy Ha;
    [discriminate|].
  destruct Hx as [|[p k] xs [Hp Hk] Hxs].
  - destruct ys as [|[q l] ys]; [|discriminate]; destruct c; [discriminate|].
    intro H; injection H as <-; split; [exact Ha|split; [cbn [bsize]; lia|]].
    change (rvalue acc=(rvalue acc+scale (bsize acc)*(0-0-0)))%Z; ring.
  - cbn [fst snd] in Hp,Hk; cbn [subtract_rec].
    destruct ys as [|[q l] ys].
    + rewrite N.min_id; destruct (subtract_part p 0 c k acc) as [mid d] eqn:E.
      unfold cut_low; rewrite N.eqb_refl; cbn [fst snd].
      intro H; destruct (subtract_part_spec p 0 c k acc mid d Hp ltac:(lia) Hk Ha E)
        as [Vm [Sm Em]].
      destruct (IH xs [] d mid out Hxs ltac:(constructor) Vm H) as [Vo [So Eo]].
      split; [exact Vo|split; [cbn [bsize]; lia|]].
      rewrite Eo,Em,Sm,value_cons,scale_add,val_zero.
      change (value []) with 0%Z; ring.
    + inversion Hy as [|? ? [Hq Hl] Hys]; subst; cbn [fst snd] in Hq,Hl.
      set (n:=N.min k l); destruct (subtract_part p q c n acc) as [mid d] eqn:E.
      intro H; destruct (subtract_part_spec p q c n acc mid d Hp Hq ltac:(unfold n; lia) Ha E)
        as [Vm [Sm Em]].
      destruct (cut_low_spec p k n xs Hp ltac:(unfold n; lia) Hxs) as [Vx [Sx Ex]].
      destruct (cut_low_spec q l n ys Hq ltac:(unfold n; lia) Hys) as [Vy [Sy Ey]].
      destruct (IH _ _ d mid out Vx Vy Vm H) as [Vo [So Eo]].
      split; [exact Vo|split; [cbn [bsize]; unfold n in *; lia|]].
      fold part in *; rewrite Eo,Em,Sm,scale_add.
      rewrite Ex,Ey; ring.
Qed.
Lemma subtract_spec xs ys out: parts_ok xs -> parts_ok ys -> subtract xs ys=Some out ->
  parts_ok out /\ bsize out<=bsize xs /\ value out=(value xs-value ys)%Z.
Proof.
  intros Hx Hy; unfold subtract; fold part in *.
  match goal with |- context[subtract_rec ?fuel ?x ?y ?c ?a]=>
    destruct (subtract_rec fuel x y c a) as [acc|] eqn:E end; [|discriminate].
  intro H; injection H as <-; rewrite fast_rev_spec.
  destruct (subtract_rec_spec _ _ _ _ _ _ Hx Hy ltac:(constructor) E) as [V [Hs He]].
  destruct (trim_rev_spec acc V) as [Vt [Ht Et]].
  split; [apply Forall_rev; exact Vt|split; [rewrite bsize_rev; cbn [bsize] in Hs; lia|]].
  change (rvalue (trim_rev acc)=(value xs-value ys))%Z.
  rewrite Et,He; change ((0+1*(value xs-value ys-0))=value xs-value ys)%Z; ring.
Qed.
End PeriodicCounter.

(* Parsing/writing binary capacity digits in the two periodic tape stacks. *)
Import ListNotations PeriodicRuntime PeriodicTape PeriodicScan PeriodicCounter.
Open Scope N_scope.

Module PeriodicCodec.
Definition stride_ok s := s=3%nat \/ s=2%nat.
Definition encode_digit stride (b:Sym) :=
  bits (fixed stride+match b with S0=>1 | S1=>0 end) stride stride.
Fixpoint encode stride xs := match xs with
  | []=>[] | b::xs=>encode_digit stride b++encode stride xs end.
Definition padded xs n := digits xs++List.repeat S0 (N.to_nat (n-bsize xs)).

Lemma encode_app stride xs ys: encode stride (xs++ys)=encode stride xs++encode stride ys.
Proof. induction xs; cbn [app encode]; rewrite ?IHxs,?app_assoc; reflexivity. Qed.
Lemma encode_length stride xs: List.length (encode stride xs)=(List.length xs*stride)%nat.
Proof.
  induction xs; cbn [encode List.length Nat.mul]; rewrite ?app_length,?IHxs; [reflexivity|].
  unfold encode_digit; rewrite bits_length; reflexivity.
Qed.
Lemma physical_facts p stride: p<4 -> stride_ok stride ->
  good (physical p stride) (2*stride) /\
  bits (physical p stride) (2*stride) stride=encode_digit stride (sym (N.odd p)) /\
  rotate_small (physical p stride) (2*stride) stride=physical (rot1 2 p) stride.
Proof.
  intros Hp Hs; assert (P: p=0 \/ p=1 \/ p=2 \/ p=3) by lia.
  destruct P as [-> | [-> | [-> | ->]]]; destruct Hs as [-> | ->];
    repeat split; vm_compute; try reflexivity; try lia; congruence.
Qed.
Lemma encode_bits p stride n: p<4 -> stride_ok stride ->
  encode stride (bits p 2 n)=bits (physical p stride) (2*stride) (n*stride).
Proof.
  revert p; induction n as [|n IH]; intros p Hp Hs; [reflexivity|].
  change (encode_digit stride (sym (N.odd p))++encode stride (bits (rot1 2 p) 2 n)=
    bits (physical p stride) (2*stride) (stride+n*stride)).
  rewrite bits_add.
  destruct (physical_facts p stride Hp Hs) as [G [E R]].
  rewrite E,R,IH; [reflexivity| |exact Hs].
  pose proof (proj1 (word_facts p 2 (good_two p Hp))) as [_ H]; change (rot1 2 p<=3) in H; lia.
Qed.
Lemma encode_word p stride n: p<4 -> stride_ok stride ->
  encode stride (word p n)=bits (physical p stride) (2*stride) (N.to_nat (n*N.of_nat stride)).
Proof. intros Hp Hs; unfold word; rewrite N2Nat.inj_mul,Nat2N.id; apply encode_bits; assumption. Qed.
Lemma padded_length xs n: bsize xs<=n -> List.length (padded xs n)=N.to_nat n.
Proof. intro H; unfold padded; rewrite app_length,digits_length,repeat_length; lia. Qed.
Lemma padded_value xs n: zcode (padded xs n)=value xs.
Proof.
  unfold padded; rewrite zcode_app.
  replace (zcode (List.repeat S0 (N.to_nat (n-bsize xs)))) with (val 0 (n-bsize xs))
    by (unfold val,word; now rewrite bits_zero).
  rewrite val_zero; unfold value; ring.
Qed.
Lemma padded_unique xs n ds: bsize xs<=n -> List.length ds=N.to_nat n -> value xs=zcode ds ->
  padded xs n=ds.
Proof.
  intros Hs Hl Hv; apply code_inj; [rewrite padded_length by exact Hs; congruence|].
  apply N2Z.inj; change (zcode (padded xs n)=zcode ds); rewrite padded_value; exact Hv.
Qed.
Lemma put_parts_spec xs stride s: parts_ok xs -> stride_ok stride -> valid s ->
  valid (put_parts xs stride s) /\ denote (put_parts xs stride s)=encode stride (digits xs) *> denote s.
Proof.
  intros H; induction H as [|[p n] xs [Hp Hn] Hxs IH]; intros Hstride Hs.
  - split; [exact Hs|reflexivity].
  - cbn [fst snd] in Hp,Hn; destruct (IH Hstride Hs) as [V E].
    cbn [put_parts]; destruct (push_spec (physical p stride) (2*stride) (n*N.of_nat stride)
      (put_parts xs stride s) (proj1 (physical_facts p stride Hp Hstride)) V) as [V' E'].
    split; [exact V'|rewrite E',E,<-encode_word by assumption].
    cbn [digits]; rewrite encode_app,Str_app_assoc; reflexivity.
Qed.
Lemma put_spec xs n stride s: parts_ok xs -> bsize xs<=n -> stride_ok stride -> valid s ->
  valid (put xs n stride s) /\ denote (put xs n stride s)=
    encode stride (padded xs n) *> denote (drop (n*N.of_nat stride) s).
Proof.
  intros Hxs Hn Hstride Hs; unfold put.
  destruct (push_spec (physical 0 stride) (2*stride) ((n-bsize xs)*N.of_nat stride)
    (drop (n*N.of_nat stride) s) (proj1 (physical_facts 0 stride ltac:(lia) Hstride))
    (drop_valid _ _ Hs)) as [V E].
  destruct (put_parts_spec xs stride _ Hxs Hstride V) as [V' E']; split; [exact V'|].
  rewrite E',E,<-encode_word by (try assumption; lia).
  unfold padded,word; rewrite bits_zero,encode_app,Str_app_assoc; reflexivity.
Qed.

Definition bulk_check p w := forallb (fun stride=>
  match bulk_pattern (Bl p w 64) stride with
  | None=>true | Some q=>andb (N.ltb q 4)
      (N.eqb (prefix p w (Nat.lcm w (2*stride)))
        (prefix (physical q stride) (2*stride) (Nat.lcm w (2*stride)))) end) [3;2]%nat.
Lemma bulk_checked: short_check bulk_check=true.
Proof. native_check_eq. Qed.
Lemma bulk_word_spec b stride p: good_block b -> stride_ok stride -> bulk_pattern b stride=Some p ->
  p<4 /\ forall n, encode stride (word p n)=bits (pat b) (width b) (N.to_nat (n*N.of_nat stride)).
Proof.
  destruct b as [q w k]; intros [Hq Hk] Hstride H; cbn [pat width len] in *.
  assert (K: N.leb (N.of_nat (Nat.lcm stride w)) 64=true).
  { destruct Hq as [Hw _]; destruct Hstride as [-> | ->];
      destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try lia; reflexivity. }
  assert (E: bulk_pattern (Bl q w 64) stride=Some p).
  { unfold bulk_pattern in H |- *; rewrite bulk_cached_spec in H |- *.
    unfold bulk_info in H |- *; cbn [pat width len] in H |- *; rewrite K.
    destruct (N.leb (N.of_nat (Nat.lcm stride w)) k); [exact H|discriminate]. }
  pose proof (short_check_spec _ bulk_checked q w Hq) as C.
  unfold bulk_check in C; rewrite forallb_forall in C.
  specialize (C stride ltac:(destruct Hstride as [-> | ->]; cbn; tauto)).
  rewrite E,Bool.andb_true_iff,N.ltb_lt,N.eqb_eq in C; destruct C as [Hp C].
  split; [exact Hp|intro n; rewrite encode_word by assumption; symmetry].
  apply common_period; [exact Hq|apply physical_facts; assumption|exact C].
Qed.
Definition consumes stride n ds s := List.length ds=N.to_nat n /\
  take_side (N.to_nat (n*N.of_nat stride)) (denote s)=encode stride ds.
Lemma consumes_nil stride s: consumes stride 0 [] s.
Proof. split; reflexivity. Qed.
Lemma consumes_app stride n m xs ys s: valid s -> consumes stride n xs s ->
  consumes stride m ys (drop (n*N.of_nat stride) s) -> consumes stride (n+m) (xs++ys) s.
Proof.
  intros Hs [Ln En] [Lm Em]; split; [rewrite app_length,Ln,Lm,N2Nat.inj_add; reflexivity|].
  rewrite N.mul_add_distr_r,N2Nat.inj_add,take_side_add,encode_app,En.
  rewrite <-drop_spec by exact Hs; now rewrite Em.
Qed.
Lemma consumes_decompose stride n ds s: valid s -> consumes stride n ds s ->
  denote s=encode stride ds *> denote (drop (n*N.of_nat stride) s).
Proof.
  intros Hs [_ E]; rewrite (take_skip (N.to_nat (n*N.of_nat stride)) (denote s)) at 1.
  rewrite E,<-drop_spec by exact Hs; reflexivity.
Qed.
Lemma consumes_bulk b s stride p n: valid (b::s) -> stride_ok stride -> bulk_pattern b stride=Some p ->
  n<=len b/N.of_nat stride -> consumes stride n (word p n) (b::s).
Proof.
  intros Hs Hstride E Hn; inversion Hs as [|? ? Hb Htail]; subst.
  split; [apply word_length|rewrite (proj2 (bulk_word_spec b stride p Hb Hstride E))].
  assert (L: n*N.of_nat stride<=len b).
  { pose proof (N.div_mod (len b) (N.of_nat stride) ltac:(destruct Hstride as [-> | ->]; discriminate)); nia. }
  rewrite denote_cons,take_side_prefix by (rewrite block_length; lia).
  unfold block_bits; apply bits_firstn; lia.
Qed.
Lemma code_bound xs: code xs<2^N.of_nat (List.length xs).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  cbn [code List.length]; rewrite Nat2N.inj_succ,N.pow_succ_r'; destruct x; cbn [digit]; nia.
Qed.
Definition single_check p w := if orb (Nat.eqb w 3) (Nat.eqb w 2) then
  if N.eqb (N.land p (mask w-1)) (fixed w)
  then N.eqb (prefix (fixed w+N.b2n (N.odd p)) w w) p else true else true.
Lemma single_checked: short_check single_check=true.
Proof. native_check_eq. Qed.
Lemma word_bit b: word (N.b2n b) 1=[sym b].
Proof. destruct b; reflexivity. Qed.
Lemma consumes_one stride s: stride_ok stride -> valid s ->
  N.land (peek stride s) (mask stride-1)=fixed stride ->
  consumes stride 1 (word (N.b2n (negb (N.odd (peek stride s)))) 1) s.
Proof.
  intros Hstride Hs E; set (p:=peek stride s) in *.
  assert (Gp: good p stride).
  { split; [destruct Hstride as [-> | ->]; lia|].
    pose proof (code_bound (take_side stride (denote s))) as B.
    rewrite take_side_length,<-peek_spec in B by exact Hs; fold p in B.
    unfold mask; rewrite N.shiftl_mul_pow2,N.mul_1_l; lia. }
  pose proof (short_check_spec _ single_checked p stride Gp) as C.
  unfold single_check in C.
  assert (T: orb (Nat.eqb stride 3) (Nat.eqb stride 2)=true)
    by (destruct Hstride as [-> | ->]; reflexivity).
  rewrite T,E,N.eqb_refl,N.eqb_eq in C.
  split; [apply word_length|].
  rewrite N.mul_1_l,Nat2N.id.
  assert (D: encode stride (word (N.b2n (negb (N.odd p))) 1)=bits p stride stride).
  { rewrite word_bit; cbn [encode].
    rewrite app_nil_r; unfold encode_digit,sym; destruct (N.odd p); cbn [N.b2n] in C |- *;
      apply prefix_eq; rewrite (proj2 (proj2 (word_facts _ _ Gp))); exact C. }
  rewrite D; apply code_inj; [rewrite take_side_length,bits_length; reflexivity|].
  rewrite <-peek_spec,bits_code by exact Hs; symmetry; apply word_facts,Gp.
Qed.
Lemma consumes_blank n: consumes 3 n (word 3 n) [].
Proof.
  split; [apply word_length|rewrite encode_word by (unfold stride_ok; auto; lia)].
  change (physical 3 3) with 0; rewrite bits_zero.
  change (take_side (N.to_nat (n*N.of_nat 3)) 0inf=List.repeat S0 (N.to_nat (n*N.of_nat 3))).
  induction (N.to_nat (n*N.of_nat 3)) as [|k IH]; [reflexivity|].
  change (S0::take_side k 0inf=S0::List.repeat S0 k); now rewrite IH.
Qed.

Definition parsed stride limit s acc done res := let '(xs,k):=res in
  exists n ds, n<=limit /\ k=done+n /\ consumes stride n ds s /\
    parts_ok xs /\ bsize xs<=bsize acc+n /\ value xs=zcode (rdigits acc++ds).
Lemma parsed_stop stride limit s acc done: parts_ok acc ->
  parsed stride limit s acc done (fast_rev (trim_rev acc),done).
Proof.
  intro H; destruct (trim_rev_spec acc H) as [V [Hs E]].
  exists 0,(@nil Sym); split; [lia|split; [lia|split; [apply consumes_nil|]]].
  rewrite fast_rev_spec; split; [apply Forall_rev,V|split; [rewrite bsize_rev; lia|]].
  rewrite app_nil_r; exact E.
Qed.
Lemma parsed_add stride limit s acc done p n res: p<4 -> n<=limit -> parts_ok acc -> valid s ->
  consumes stride n (word p n) s ->
  parsed stride (limit-n) (drop (n*N.of_nat stride) s) (add_part p n acc) (done+n) res ->
  parsed stride limit s acc done res.
Proof.
  intros Hp Hn Ha Hs C; destruct res as [xs k]; intros [m [ds [Hm [K [Cm [V [L E]]]]]]].
  exists (n+m),(word p n++ds); split; [lia|split; [lia|split; [eapply consumes_app; eassumption|]]].
  split; [exact V|split; [rewrite add_part_size in L by assumption; lia|]].
  rewrite (proj2 (add_part_spec p n acc Hp Ha)),<-app_assoc in E; exact E.
Qed.
Lemma parse_rec_spec fuel stride limit s acc done: stride_ok stride -> valid s -> parts_ok acc ->
  parsed stride limit s acc done (parse_rec fuel stride limit s acc done).
Proof.
  revert limit s acc done; induction fuel as [|fuel IH]; intros limit s acc done Hstride Hs Ha;
    cbn [parse_rec]; [apply parsed_stop,Ha|].
  destruct (N.eqb_spec limit 0); [apply parsed_stop,Ha|].
  destruct s as [|b s].
  - destruct (Nat.eqb_spec stride 3).
    + subst stride; eapply parsed_add with (p:=3) (n:=limit); try eassumption; try lia.
      * apply consumes_blank.
      * apply parsed_stop,add_part_spec; auto; lia.
    + apply parsed_stop,Ha.
  - destruct (bulk_pattern b stride) as [p|] eqn:E.
    + inversion Hs as [|? ? Hb Htail]; subst.
      destruct (bulk_word_spec b stride p Hb Hstride E) as [Hp _].
      eapply parsed_add with (p:=p) (n:=N.min limit (len b/N.of_nat stride)); try eassumption;
        [apply N.le_min_l|eapply consumes_bulk; eauto; apply N.le_min_r|].
      apply IH; try assumption; [apply drop_valid,Hs|apply add_part_spec; assumption].
    + destruct (N.eqb_spec (N.land (peek stride (b::s)) (mask stride-1)) (fixed stride)).
      * eapply parsed_add with (p:=N.b2n (negb (N.odd (peek stride (b::s))))) (n:=1);
          try eassumption; [destruct (N.odd (peek stride (b::s))); cbn; lia|lia|apply consumes_one; assumption|].
        rewrite N.mul_1_l; apply IH; try assumption; [apply drop_valid,Hs|].
        apply add_part_spec; [destruct (N.odd (peek stride (b::s))); cbn; lia|assumption].
      * apply parsed_stop,Ha.
Qed.
Lemma parse_spec stride limit s xs n: stride_ok stride -> valid s -> parse stride limit s=(xs,n) ->
  parts_ok xs /\ n<=limit /\ bsize xs<=n /\
  denote s=encode stride (padded xs n) *> denote (drop (n*N.of_nat stride) s).
Proof.
  intros Hstride Hs E; unfold parse in E.
  match type of E with parse_rec ?fuel _ _ _ _ _ = _=>
    pose proof (parse_rec_spec fuel stride limit s [] 0 Hstride Hs ltac:(constructor)) as H end.
  fold part in *; rewrite E in H; destruct H as [m [ds [Hm [K [C [V [L Hv]]]]]]].
  cbn [bsize rdigits digits rev app] in K,L,Hv; subst n.
  split; [exact V|split; [exact Hm|split; [exact L|]]].
  change (denote s=encode stride (padded xs m) *> denote (drop (m*N.of_nat stride) s)).
  rewrite (padded_unique xs m ds L (proj1 C) Hv); apply consumes_decompose; assumption.
Qed.
End PeriodicCodec.

(* Connect the compressed capacity arithmetic to the two ordinary TM counters. *)
Import ListNotations PeriodicRuntime PeriodicTape PeriodicScan PeriodicCounter PeriodicCodec.
Close Scope Z_scope.
Close Scope N_scope.

Module PeriodicMachine.
Definition addN p k := match k with N0=>p | Npos k=>Pos.add p k end.
Lemma addN_succ p k: addN p (N.succ k)=addN (Pos.succ p) k.
Proof. destruct k; cbn [addN N.succ]; lia. Qed.
Fixpoint counter (xs:list Sym) : positive := match xs with
  | []=>xH | S0::xs=>xI (counter xs) | S1::xs=>xO (counter xs) end.
Lemma counter_rest xs: rest (counter xs)=code xs.
Proof.
  induction xs as [|[] xs IH]; cbn [counter code digit]; [reflexivity| |].
  - rewrite rest_mul2add1,IH; lia.
  - rewrite rest_mul2,IH; lia.
Qed.
Lemma counter_total xs:
  (N.pos (counter xs)+code xs=N.pos (pow2' (List.length xs)))%N.
Proof.
  induction xs as [|[] xs IH]; cbn [counter code digit List.length pow2']; lia.
Qed.
Lemma counter_change xs ys k: List.length xs=List.length ys ->
  (code ys+k=code xs)%N -> counter ys=addN (counter xs) k.
Proof.
  intros Hl Hv; pose proof (counter_total xs); pose proof (counter_total ys).
  rewrite Hl in H; destruct k; cbn [addN]; lia.
Qed.
Lemma counter_encode stride xs r:
  encode stride xs *> r=BinaryCounter (encode_digit stride S1) (encode_digit stride S0) r (counter xs).
Proof. induction xs as [|[] xs IH]; cbn [counter encode BinaryCounter]; rewrite ?Str_app_assoc,?IH; reflexivity. Qed.

Section Machine.
Variable tm:TM.
Variables QL QR:Q.
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.

Hypothesis ASweep: forall l r n,
  l <* [1]^^n <{{QL}} [1] *> r -[tm]->*
  l <{{QL}} [1]^^n *> [1] *> r.

Lemma paired k p q l r: (k<=rest p)%N -> (k<=rest q)%N ->
  BinaryCounter ld0 ld1 l p |> BinaryCounter rd0 rd1 r q -[tm]->*
  BinaryCounter ld0 ld1 l (addN p k) |> BinaryCounter rd0 rd1 r (addN q k).
Proof.
  revert p q; induction k using N.peano_ind; intros p q Hp Hq.
  - apply evstep_refl.
  - assert (Hp0: rest p<>0%N) by lia; assert (Hq0: rest q<>0%N) by lia.
    pose proof (rest_S p Hp0); pose proof (rest_S q Hq0); rewrite !addN_succ.
    eapply evstep_trans.
    + apply progress_evstep; apply BinaryCounter.RInc.
      * intros; change (rd0^^n *> rd1 *> r0) with (rd0^^n *> [1] *> [0;0] *> r0); apply RInc.
      * apply not_full_iff_rest,Hq0.
    + eapply evstep_trans.
      * apply progress_evstep; apply BinaryCounter.LInc; [apply LInc|apply not_full_iff_rest,Hp0].
      * apply IHk; lia.
Qed.
Lemma paired_words k a b a' b' l r:
  List.length a=List.length a' -> List.length b=List.length b' ->
  (code a'+k=code a)%N -> (code b'+k=code b)%N ->
  (encode 2 a *> l) |> encode 3 b *> r -[tm]->*
  (encode 2 a' *> l) |> encode 3 b' *> r.
Proof.
  intros La Lb Ea Eb; rewrite !counter_encode.
  rewrite (counter_change a a' k La Ea),(counter_change b b' k Lb Eb).
  apply paired; rewrite counter_rest; lia.
Qed.
Lemma paired_capacity ticks a b a' b' n m l r:
  (bsize a<=n)%N -> (bsize b<=m)%N -> (bsize a'<=n)%N -> (bsize b'<=m)%N ->
  value a=(value a'+Z.of_N ticks)%Z -> value b=(value b'+Z.of_N ticks)%Z ->
  (encode 2 (padded a n) *> l) |> encode 3 (padded b m) *> r -[tm]->*
  (encode 2 (padded a' n) *> l) |> encode 3 (padded b' m) *> r.
Proof.
  intros Ha Hb Ha' Hb' Ea Eb; apply paired_words with (k:=ticks).
  - rewrite !padded_length by assumption; reflexivity.
  - rewrite !padded_length by assumption; reflexivity.
  - apply N2Z.inj; rewrite N2Z.inj_add; change (zcode (padded a' n)+Z.of_N ticks=zcode (padded a n))%Z.
    rewrite !padded_value; lia.
  - apply N2Z.inj; rewrite N2Z.inj_add; change (zcode (padded b' m)+Z.of_N ticks=zcode (padded b m))%Z.
    rewrite !padded_value; lia.
Qed.

Lemma prefix2 l: valid l -> peek 2 l=2%N ->
  denote l=[0;1] *> denote (drop 2 l).
Proof.
  intros Hl E; assert (G: good 2 2) by (split; [lia|vm_compute; discriminate]).
  pose proof (matches_decompose 2 2 1 l G Hl (matches_one 2 2 l G Hl E)) as H.
  change (denote l=[0;1] *> denote (drop 2 l)) in H; exact H.
Qed.
Lemma pair_run l r a b n m a' b' ticks:
  valid l -> valid r -> peek 2 l=2%N ->
  parse 2 100000000 (drop 2 l)=(a,n) -> parse 3 (n+1) r=(b,m) ->
  parts_ok a' -> parts_ok b' -> (bsize a'<=n)%N -> (bsize b'<=m)%N ->
  value a=(value a'+Z.of_N ticks)%Z -> value b=(value b'+Z.of_N ticks)%Z ->
  let t:=(QR,push 2 2 2 (put a' n 2 (drop 2 l)),put b' m 3 r) in
  valid_state t /\ config (QR,l,r) -[tm]->* config t.
Proof.
  intros Hl Hr Hprefix Pa Pb Va' Vb' Ha' Hb' Ea Eb.
  destruct (parse_spec 2 100000000 (drop 2 l) a n ltac:(right; reflexivity) (drop_valid _ _ Hl) Pa)
    as [Va [_ [Ha La]]].
  destruct (parse_spec 3 (n+1) r b m ltac:(left; reflexivity) Hr Pb) as [Vb [_ [Hb Lb]]].
  destruct (put_spec a' n 2 (drop 2 l) Va' Ha' ltac:(right; reflexivity) (drop_valid _ _ Hl)) as [Vl Ll].
  destruct (put_spec b' m 3 r Vb' Hb' ltac:(left; reflexivity) Hr) as [Vr Lr].
  destruct (push_spec 2 2 2 _ ltac:(split; [lia|vm_compute; discriminate]) Vl) as [Vl' Ll'].
  split; [split; assumption|].
  unfold config; rewrite Ll',Ll,Lr,(prefix2 l Hl Hprefix),La,Lb.
  change ((encode 2 (padded a n) *> denote (drop (n*2) (drop 2 l))) |>
    encode 3 (padded b m) *> denote (drop (m*3) r) -[tm]->*
    (encode 2 (padded a' n) *> denote (drop (n*2) (drop 2 l))) |>
    encode 3 (padded b' m) *> denote (drop (m*3) r)).
  eapply paired_capacity; eassumption.
Qed.
Lemma pair_spec s t: valid_state s -> pair QR s=Some t ->
  valid_state t /\ config s -[tm]->* config t.
Proof.
  destruct s as [[q l] r]; intros [Hl Hr]; unfold pair.
  destruct (q_eqb_spec q QR); try discriminate; subst q.
  destruct (N.eqb_spec (peek 2 l) 2); try discriminate.
  destruct (N.eqb (N.land (peek 3 r) 6) 0); try discriminate.
  destruct (parse 2 100000000 (drop 2 l)) as [a n] eqn:Pa.
  destruct a as [|x a]; [discriminate|].
  destruct (parse 3 (n+1) r) as [b m] eqn:Pb.
  destruct b as [|y b]; [discriminate|].
  destruct (parse_spec _ _ _ _ _ ltac:(right; reflexivity) (drop_valid _ _ Hl) Pa) as [Va [_ [Ha _]]].
  destruct (parse_spec _ _ _ _ _ ltac:(left; reflexivity) Hr Pb) as [Vb [_ [Hb _]]].
  destruct (compare (x::a) (y::b)) eqn:E;
    match goal with |- context[subtract ?u ?v]=>destruct (subtract u v) as [out|] eqn:Hsub end;
    try discriminate; intros H; injection H as <-.
  - destruct (subtract_spec _ _ _ Va Vb Hsub) as [V [S D]].
    eapply pair_run with (a:=x::a) (b:=y::b) (ticks:=code (digits (y::b))); try eassumption.
    all: try solve [exact (Forall_nil part_ok)]; cbn [bsize]; try lia;
      try change (value []) with 0%Z; unfold value,zcode in *; lia.
  - destruct (subtract_spec _ _ _ Vb Va Hsub) as [V [S D]].
    eapply pair_run with (a:=x::a) (b:=y::b) (ticks:=code (digits (x::a))); try eassumption;
      try solve [exact (Forall_nil part_ok)]; cbn [bsize]; try lia;
      try change (value []) with 0%Z; unfold value,zcode in *; lia.
  - destruct (subtract_spec _ _ _ Va Vb Hsub) as [V [S D]].
    eapply pair_run with (a:=x::a) (b:=y::b) (ticks:=code (digits (y::b))); try eassumption;
      try solve [exact (Forall_nil part_ok)]; cbn [bsize]; try lia;
      try change (value []) with 0%Z; unfold value,zcode in *; lia.
Qed.

Variable hs:list shift.
Hypothesis Hshifts: Forall (shift_valid tm) hs.
Lemma a_sweep_spec s t: valid_state s -> a_sweep QL s=Some t ->
  valid_state t /\ config s -[tm]->* config t.
Proof.
  destruct s as [[q l] r]; intros [Hl Hr]; unfold a_sweep.
  destruct (N.eqb_spec (peek 1 (drop 1 r)) 1) as [Hguard|Hguard]; try discriminate.
  unfold try_shift; cbn [sq sd sw sin sout].
  destruct (q_eqb_spec q QL); try discriminate; subst q.
  set (x:=push1 (top r) l); set (n:=count 1 1 x).
  destruct (N.ltb 1 n); try discriminate; intro H; injection H as <-.
  assert (G: good 1 1) by (split; [lia|vm_compute; discriminate]).
  destruct (push_top r l Hr Hl) as [Hx Ex]; change (valid x) in Hx.
  destruct (push_words 1 1 n (drop 1 r) G (drop_valid _ _ Hr)) as [Vr Er].
  destruct (left_state_spec QL (drop (n*N.of_nat 1) x) _
    (drop_valid _ _ Hx) Vr) as [V E].
  split; [exact V|].
  eapply evstep_trans; [apply evstep_refl'; exact (turn_state QL l r Hl Hr)|].
  rewrite Er in E; eapply evstep_trans; [|apply evstep_refl'; symmetry; exact E].
  change (denote x <{{QL}} denote (drop 1 r) -[tm]->*
    denote (drop (n*N.of_nat 1) x) <{{QL}} [1]^^(N.to_nat n) *> denote (drop 1 r)).
  pose proof (matches_decompose 1 1 1 (drop 1 r) G (drop_valid _ _ Hr)
    (matches_one 1 1 (drop 1 r) G (drop_valid _ _ Hr) Hguard)) as R.
  change (denote (drop 1 r)=[1] *> denote (drop 1 (drop 1 r))) in R.
  rewrite (count_spec 1 1 x G Hx),R.
  apply ASweep.
Qed.
Definition next s : state+unit := match a_sweep QL s with
  | Some t=>inl t | None=>match event tm QR hs s with
    | (_,Some t)=>inl t | (_,None)=>inr tt end end.
Lemma next_spec s: valid_state s -> match next s with
  | inl t=>valid_state t /\ config s -[tm]->* config t | inr _=>halts tm (config s) end.
Proof.
  intro Hs; unfold next; destruct (a_sweep QL s) as [u|] eqn:U.
  { eapply a_sweep_spec; eassumption. }
  unfold event; destruct (pair QR s) as [t|] eqn:E.
  - apply pair_spec with (s:=s); assumption.
  - destruct (scan hs s) as [t|] eqn:G.
    + eapply scan_spec; eassumption.
    + destruct (primitive tm s) as [t|] eqn:H.
      * destruct (primitive_spec tm s t Hs H) as [V Step]; split; [exact V|].
        apply step_c_spec in Step; eapply evstep_step; [exact Step|apply evstep_refl].
      * apply primitive_halt; assumption.
Qed.
Definition check_from (initial:state) fuel := match N_iter_until next (inl initial) fuel with
  | inr _=>true | inl _=>false end.
Lemma check_from_spec initial fuel: valid_state initial -> check_from initial fuel=true -> halts tm (config initial).
Proof.
  intro Vi; pose proof (@N_iter_until_spec state unit next (inl initial) fuel
    (fun s=>valid_state s /\ config initial -[tm]->* config s) (fun _=>halts tm (config initial))) as H.
  assert (K: forall s, valid_state s /\ config initial -[tm]->* config s ->
    match next s with
    | inl t=>valid_state t /\ config initial -[tm]->* config t
    | inr _=>halts tm (config initial) end).
  { intros s [Vs Es]; pose proof (next_spec s Vs) as E; destruct (next s).
    - destruct E as [V E]; split; [exact V|eapply evstep_trans; eassumption].
    - eapply halts_evstep; eassumption. }
  specialize (H K (conj Vi (evstep_refl _ _))); unfold check_from.
  destruct (N_iter_until next (inl initial) fuel); cbn in H |- *; intros E; try discriminate; exact H.
Qed.
End Machine.
End PeriodicMachine.

Import ListNotations PeriodicRuntime PeriodicTape PeriodicScan.
Close Scope Z_scope.
Close Scope N_scope.

Module TM165.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_1LD---").
Notation "l |> r" := (l <* <[1;0] {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Lemma LInc l r n:
  l <* <[1;0] <* <[1;1]^^n <| r -[tm]->+ l <* <[1;1] <* <[1;0]^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> [1;0;0]^^n *> [0] *> r -[tm]->+ l <| [0;0;0]^^n *> [1] *> r.
Proof. es. Qed.
Lemma ASweep l r n:
  l <* [1]^^n <{{A}} [1] *> r -[tm]->*
  l <{{A}} [1]^^n *> [1] *> r.
Proof. rewrite lpow_shift'. shift_rule; es. Qed.
Definition shifts := [Sh C L 1 1 0; Sh B R 2 3 2; Sh B R 3 1 7].
Ltac short_word_good := split; [lia|vm_compute; discriminate].
Ltac expand_short_words := repeat match goal with
  | |- context[bits ?p ?w ?n]=>let xs:=eval vm_compute in (bits p w n) in
    change (bits p w n) with xs end.
Lemma shifts_spec: Forall (shift_valid tm) shifts.
Proof.
  repeat (constructor; [unfold shift_valid; cbn [sq sd sw sin sout];
    split; [short_word_good|split; [short_word_good|intros; expand_short_words; shift_rule; es]]|]).
  constructor.
Qed.
Definition check fuel := PeriodicMachine.check_from tm A B shifts (A,[],[]) fuel.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof.
  unfold check; apply PeriodicMachine.check_from_spec;
    [apply LInc|apply RInc|apply ASweep|apply shifts_spec|split; constructor].
Qed.
Theorem halt: halts tm c0.
Proof. apply (check_spec 1048576%N). native_check_eq. Time Qed.
End TM165.

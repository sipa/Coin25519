Require Import Bvector.
Require Import Eqdep_dec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition bCompare (x y : bool) : comparison :=
match x, y with
| false, false => Eq
| false, true  => Lt
| true , false => Gt
| true , true  => Eq
end.

Lemma bCompare_CompOpp : forall b1 b2, bCompare b1 b2 = CompOpp (bCompare b2 b1).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma bCompare_refl : forall b, bCompare b b = Eq.
Proof. intros [|]; reflexivity. Qed.

Lemma bCompare_elim : forall P : bool -> bool -> comparison -> Type,
  (forall b, P b b Eq) ->
  (P false true Lt) ->
  (P true false Gt) ->
  forall b1 b2, P b1 b2 (bCompare b1 b2).
Proof.
intros P H0 H1 H2 [|] [|]; auto.
Qed.

Lemma vector_rect2:
  forall (A : Type) (P : forall n : nat, vector A n -> vector A n -> Type),
  P 0 (Vnil A) (Vnil A) ->
  (forall (a1 a2 : A) (n : nat) (v1 v2 : vector A n),
   P n v1 v2 -> P (S n) (Vcons A a1 n v1) (Vcons A a2 n v2)) ->
  forall (n : nat) (v1 v2 : vector A n), P n v1 v2.
Proof.
intros A P H0 H1 n v1 v2.
change v2 with (eq_rect n (vector A) v2 n (eq_refl n)).
generalize (eq_refl n).
set (a:=n).
unfold a at 1 4.
revert v2.
induction v1; intros v2; dependent inversion v2; intros e.
 replace e with (refl_equal 0);[|apply UIP_dec; decide equality].
 assumption.
replace e with (refl_equal (S n));[|apply UIP_dec; decide equality].
apply H1.
apply (IHv1 v (refl_equal n)).
Qed.

Lemma vector_dec : forall A, (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
 forall n (v1 v2 : vector A n), {v1 = v2} + {v1 <> v2}.
Proof.
intros A A_dec.
set (P := fun n (v1 v2 : vector A n) => {v1 = v2} + {v1 <> v2}).
apply (vector_rect2 (A := A) (P := P)).
 left; reflexivity.
intros a1 a2 n v1 v2 [IH|IH].
 rewrite IH.
 case (A_dec a1 a2); intros Ha.
  rewrite Ha.
  left; reflexivity.
 right; intros H.
 apply Ha.
 injection H; auto.
right; intros H.
apply IH.
refine (@inj_pair2_eq_dec _ _ (fun n => vector A n) _ _ _ _).
 decide equality.
injection H.
auto.
Defined.

Section PatriciaTrie.

Variable A:Set.

Inductive PatriciaTrieR : nat -> Set :=
| Tip : A -> PatriciaTrieR 0
| Arm : bool -> forall n, PatriciaTrieR n -> PatriciaTrieR (S n)
| Branch : forall n, PatriciaTrieR n -> PatriciaTrieR n -> PatriciaTrieR (S n).

Definition PatriciaTrie n := option (PatriciaTrieR n).

Fixpoint singletonR (n : nat) (k:Bvector n) (v:A) : PatriciaTrieR n := 
match k in vector _ n return PatriciaTrieR n with
| Vnil => Tip v
| Vcons r m k' => Arm r (singletonR k' v)
end.

Definition singleton n k v : PatriciaTrie n := option_map (singletonR k) v.

Fixpoint getR n (k:Bvector n) : PatriciaTrieR n -> option A :=
match k with
| Vnil => fun t =>
  match t with
  | Tip v => Some v
  | _ => @id
  end
| Vcons b n k' => fun t =>
  match t with
  | Arm b0 m t0 => fun rec =>
    match bCompare b b0 with
    | Eq => rec t0
    | Lt | Gt => None
    end
  | Branch m t0 t1 => fun rec =>
    if b then rec t1 else rec t0
  end (fun t => getR k' t)
end.

Definition get n (k:Bvector n) (ot:PatriciaTrie n) : option A :=
match ot with
| Some t => getR k t
| None   => None
end.

Fixpoint setR n (k:Bvector n) : PatriciaTrieR n -> option A -> PatriciaTrie n :=
match k with
| Vnil => fun t =>
  match t with
  | Tip v => option_map Tip
  | _ => @id
  end
| Vcons b n k' => fun t =>
  match t with
  | Arm b0 m t0 => fun k' rec =>
    match bCompare b b0 with
    | Lt => fun ov =>
      match ov with
      | None => Some (Arm b0 t0)
      | Some v => Some (Branch (singletonR k' v) t0)
      end
    | Eq => fun ov => option_map (@Arm b0 m) (rec t0 ov)
    | Gt => fun ov =>
      match ov with
      | None => Some (Arm b0 t0)
      | Some v => Some (Branch t0 (singletonR k' v))
      end
    end
  | Branch m t0 t1 => fun _ rec =>
    if b
    then
     fun ov => Some
        match rec t1 ov with
        | None => Arm false t0
        | Some t1' => Branch t0 t1'
        end        
    else
     fun ov => Some
        match rec t0 ov with
        | None => Arm true t1
        | Some t0' => Branch t0' t1
        end
  end k' (fun t => setR k' t)
end.

Definition set n (k:Bvector n) (ot : PatriciaTrie n) : option A -> PatriciaTrie n :=
match ot with
| Some t => setR k t
| None   => option_map (singletonR k)
end.

Lemma lens1 : forall n (k : Bvector n) ot, set k ot (get k ot) = ot.
Proof.
intros n k [t|];try reflexivity.
change t with (eq_rec n PatriciaTrieR t n (eq_refl n)).
generalize (eq_refl n).
set (a:=n).
unfold a at 1 6 10 13.
revert t.
induction k as [|b m k];
 intros t;dependent inversion t;
  (apply K_dec_set;[intros x y; decide equality|try reflexivity]).
 simpl.
 case b; case b0; try reflexivity; simpl;
  pose (IHp := IHk p (eq_refl m));
  simpl in IHp;
  rewrite IHp;
  reflexivity.
simpl.
case b;
 pose (IHp := fun p => IHk p (eq_refl m));
 simpl in IHp;
 rewrite IHp;
 reflexivity.
Qed.

Lemma getR_singletonR : forall n (k : Bvector n) nv, getR k (singletonR k nv) = Some nv.
Proof.
intros n k nv.
induction k as [|b m k].
 reflexivity.
case b; auto.
Qed.

Lemma lens2 : forall n (k : Bvector n) ot nv, get k (set k ot nv) = nv.
Proof.
intros n k [t|] nv; simpl;
 [|destruct nv as [nv|]; simpl; auto using getR_singletonR].
change t with (eq_rec n PatriciaTrieR t n (eq_refl n)).
generalize (eq_refl n).
set (a:=n).
unfold a at 1 5.
revert t.
induction k as [|b m k].
 intros t;dependent inversion t;
 (apply K_dec_set;[intros x y; decide equality|]);
 destruct nv; reflexivity.
intros t;dependent inversion t;
 (apply K_dec_set;[intros x y; decide equality|]);
 simpl (eq_rec _ _ _ _ _);
 pose (IHkp := fun p => IHk p (refl_equal m));
 simpl in IHkp.
 case b; case b0;
 destruct nv as [nv|]; simpl; try auto using getR_singletonR;
 apply (fun x => eq_trans x (IHkp p));
 case (setR _ _ _); reflexivity.
case b;
 [apply (fun x => eq_trans x (IHkp p0))
 |apply (fun x => eq_trans x (IHkp p))
 ]; simpl; case (setR _ _ _); reflexivity.
Qed.

Lemma setR_singletonR : forall n (k : Bvector n) nv1 nv2, setR k (singletonR k nv1) nv2 = option_map (singletonR k) nv2.
Proof.
intros n k nv1 nv2.
induction k as [|b m k].
 reflexivity.
case b; simpl; rewrite IHk; destruct nv2; reflexivity.
Qed.

Lemma lens3 : forall n (k : Bvector n) ot nv1 nv2, set k (set k ot nv1) nv2 = set k ot nv2.
Proof.
intros n k [t|] nv1 nv2; simpl;
 [|destruct nv1 as [nv1|]; simpl; auto using setR_singletonR].
change t with (eq_rec n PatriciaTrieR t n (eq_refl n)).
generalize (eq_refl n).
set (a:=n).
unfold a at 1 6 9.
revert t.
induction k as [|b m k].
 intros t;dependent inversion t.
 (apply K_dec_set;[intros x y; decide equality|]).
 destruct nv1; reflexivity.
intros t;dependent inversion t;
 (apply K_dec_set;[intros x y; decide equality|]);
 simpl (eq_rec _ _ _ _ _);
 pose (IHkp := fun p => IHk p (refl_equal m));
 simpl in IHkp.
 case b; case b0;
  destruct nv2 as [nv2|]; simpl;
 try solve
 [rewrite <- IHkp;
  case (setR _ _ _); reflexivity
 |destruct nv1 as [nv1|];
  simpl; try reflexivity;
  (rewrite setR_singletonR; auto)
 ].
case b; simpl; rewrite <- IHkp;
 simpl; case (setR _ _ _); try reflexivity;
 destruct nv2 as [nv2|];reflexivity.
Qed.

Lemma singleton_indep : forall n  (k1 k2 : Bvector n) nv1 nv2, k1 <> k2 ->
 set k2 (singleton k1 nv1) nv2 = set k1 (singleton k2 nv2) nv1.
Proof.
set (P := fun n (k1 k2 : Bvector n) => forall nv1 nv2, k1 <> k2 ->
 set k2 (singleton k1 nv1) nv2 = set k1 (singleton k2 nv2) nv1).
apply (vector_rect2 (A:=bool) (P:=P)).
 intros nv1 nv2 H.
 elim H.
 reflexivity.
intros b1 b2 n k1 k2 IH nv1 nv2.
assert (bool_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}).
 decide equality.
case (vector_dec bool_dec k1 k2).
 intros Hk; rewrite Hk.
 case (bool_dec b1 b2).
 intros Hb; rewrite Hb.
  intros H; elim H; reflexivity.
 intros Hb _.
 destruct nv1 as [nv1|]; destruct nv2 as [nv2|]; simpl; try reflexivity.
   rewrite bCompare_CompOpp.
   destruct b1 b2 (bCompare b1 b2) using bCompare_elim; try reflexivity.
   elim Hb; reflexivity.
  destruct b1 b2 (bCompare b1 b2) using bCompare_elim; try reflexivity.
  elim Hb; reflexivity.
 destruct b1 b2 (bCompare b1 b2) using bCompare_elim; try reflexivity.
 elim Hb; reflexivity.
intros Hk _.
pose (IH0 := IH nv1 nv2 Hk).
destruct nv1 as [nv1|]; destruct nv2 as [nv2|]; simpl; try reflexivity.
  rewrite bCompare_CompOpp.
  destruct b1 b2 (bCompare b1 b2) using bCompare_elim; try reflexivity.
  simpl in IH0; simpl; rewrite IH0; reflexivity.
 case (bCompare b2 b1); try reflexivity.
 simpl in IH0; simpl; rewrite IH0; reflexivity.
case (bCompare b1 b2); try reflexivity.
simpl in IH0; simpl; rewrite <- IH0; reflexivity.
Qed.

Lemma lens_indep : forall n (k1 k2 : Bvector n) ot nv1 nv2, k1 <> k2 ->
 set k2 (set k1 ot nv1) nv2 = set k1 (set k2 ot nv2) nv1.
Proof.
intros n k1 k2 [t|];[simpl|apply singleton_indep].
revert n k1 k2 t.
set (P := fun n k1 k2 => forall (t : PatriciaTrieR n)
  (nv1 nv2 : option A),
  k1 <> k2 -> set k2 (setR k1 t nv1) nv2 = set k1 (setR k2 t nv2) nv1).
apply (vector_rect2 (A:=bool) (P:=P)).
 intros ot n1 n2 H.
 elim H.
 reflexivity.
intros b1 b2 n k1 k2 IH t.
compare b1 b2.
 intros Hb.
 rewrite Hb.
 assert (bool_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}).
  decide equality.
 case (vector_dec bool_dec k1 k2).
  intros Hk nv1 nv2.
  rewrite Hk.
  intros H.
  elim H.
  reflexivity.
 intros H nv1 nv2 _.
 change t with (eq_rec (S n) PatriciaTrieR t (S n) (eq_refl (S n))).
  generalize (eq_refl (S n)).
 set (a:=(S n)).
 unfold a at 1 6 10.
 dependent inversion t;
  (apply K_dec_set;[intros x y; decide equality|]);
  simpl (eq_rec _ _ _ _ _).
  simpl.
  apply bCompare_elim.
    intros b0.
    generalize (IH p nv1 nv2 H).
    case (setR k1 p nv1); case (setR k2 p nv2); simpl.
       intros p0 p1 Hset.
       rewrite bCompare_refl.
       congruence.
      intros p0 Hset.
      rewrite bCompare_refl, Hset.
      destruct nv1; reflexivity.
     intros p0 Hset.
     rewrite bCompare_refl, <- Hset.
     destruct nv2; reflexivity.
    destruct nv1; destruct nv2; simpl; solve[ discriminate | congruence].
   generalize (singleton_indep nv1 nv2 H).
   destruct nv1; destruct nv2; simpl; try reflexivity;
      intros Hset; (rewrite Hset || rewrite <- Hset); reflexivity.
  generalize (singleton_indep nv1 nv2 H).
  destruct nv1; destruct nv2; simpl; try reflexivity;
     intros Hset; (rewrite Hset || rewrite <- Hset); reflexivity.
 case b2;[set (p2 := p0)|set (p2 := p)];
  (generalize (IH p2 nv1 nv2 H); simpl (setR _ _ _);
   destruct (setR k1 p2 nv1); destruct (setR k2 p2 nv2); simpl; intros Hset;
   [rewrite Hset; reflexivity
   |rewrite Hset; destruct nv1; reflexivity
   |rewrite <- Hset; destruct nv2; reflexivity
   |destruct nv1; destruct nv2; try discriminate; try reflexivity;
    injection Hset; congruence]).
intros Hb nv1 nv2 _.
replace b2 with (negb b1) by
 (destruct b1; destruct b2; try solve[reflexivity|elim Hb; reflexivity]).
clear b2 Hb.
change t with (eq_rec (S n) PatriciaTrieR t (S n) (eq_refl (S n))).
 generalize (eq_refl (S n)).
set (a:=(S n)).
unfold a at 1 6 10.
dependent inversion t;
 (apply K_dec_set;[intros x y; decide equality|]);
 simpl (eq_rec _ _ _ _ _).
 simpl.
 apply bCompare_elim.
   intros [|];
    destruct nv2; simpl; destruct (setR k1 p nv1); reflexivity.
  destruct nv1; simpl; destruct (setR k2 p nv2); reflexivity.
 destruct nv1; simpl; destruct (setR k2 p nv2); reflexivity.
case b1; simpl.
 case_eq (setR k1 p0 nv1); [intros p2|]; intros Hset;
  destruct (setR k2 p nv2);
   rewrite Hset; reflexivity.
case_eq (setR k1 p nv1); [intros p2|]; intros Hset;
 destruct (setR k2 p0 nv2);
  rewrite Hset; reflexivity.
Qed.

(* Note: the merkle hashing of the patricia tree should hash the keys with the values.
         In the case that they key is the hash of the value, then the key will be the hash of the value, so need not be included 
*)

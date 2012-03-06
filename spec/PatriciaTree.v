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

Lemma getR_singletonR_indep : forall n (k1 k2 : Bvector n) nv, k1 <> k2 -> getR k1 (singletonR k2 nv) = None.
Proof.
set (P := fun n (k1 k2 : Bvector n) => forall nv : A,
  k1 <> k2 -> getR k1 (singletonR k2 nv) = None).
apply (vector_rect2 (A:=bool) (P:=P)).
 intros nv.
 congruence.
unfold P; simpl.
intros b1 b2.
apply bCompare_elim; try reflexivity.
intros b n k1 k2 IH nv Hk.
apply IH.
congruence.
Qed.

Lemma get_indep : forall n (k1 k2 : Bvector n) ot nv, k1 <> k2 -> get k1 (set k2 ot nv) = get k1 ot.
Proof.
set (P := fun n (k1 k2 : Bvector n) => forall ot nv,
  k1 <> k2 -> get k1 (set k2 ot nv) = get k1 ot).
apply (vector_rect2 (A:=bool) (P:=P)); unfold P.
 congruence.
intros b1 b2 n k1 k2 IH [t|] nv Hk;
 [|destruct nv as [nv|]; simpl;
  [revert Hk; apply bCompare_elim|];
  try (intros b Hk; apply getR_singletonR_indep);
  congruence].
change t with (eq_rec (S n) PatriciaTrieR t (S n) (eq_refl (S n))).
generalize (eq_refl (S n)).
set (a:=(S n)).
unfold a at 1 6 10.
dependent inversion t;
 intros E; elim E using K_dec_set; try decide equality;
 simpl (eq_rec _ _ _ _ _).
 revert Hk.
 simpl.
 apply bCompare_elim.
   intros b0.
   apply bCompare_elim.
     intros b3 Hk.
     assert (IHp := (IH (Some p) nv)).
     simpl in IHp.
     rewrite <- IHp by congruence.
     destruct (setR k2 p nv);
      [simpl; rewrite bCompare_refl|]; reflexivity.
    destruct (setR k2 p nv); reflexivity.
   destruct (setR k2 p nv); reflexivity.
  destruct b1;
   destruct nv; try reflexivity.
  intros Hk.
  apply getR_singletonR_indep.
  congruence.
 destruct b1;
  destruct nv; try reflexivity.
 intros Hk.
 apply getR_singletonR_indep.
 congruence.
unfold set.
destruct b1.
 assert (IHp0 := (IH (Some p0) nv)).
 simpl in IHp0.
 destruct b2; simpl.
  rewrite <- IHp0 by congruence.
  destruct (setR k2 p0 nv); reflexivity.
 destruct (setR k2 p nv); reflexivity.
assert (IHp := (IH (Some p) nv)).
simpl in IHp.
destruct b2; simpl.
 destruct (setR k2 p0 nv); reflexivity.
rewrite <- IHp by congruence.
destruct (setR k2 p nv); reflexivity.
Qed.

Lemma trieR_nonempty : forall n (t : PatriciaTrieR n), {p : (Bvector n*A) | getR (fst p) t = Some (snd p)}.
Proof.
intros n t.
induction t.
  exists (pair (Vnil _) a).
  reflexivity.
 destruct IHt as [[k a] IHt].
 exists (pair (Vcons _ b _ k) a).
 simpl; rewrite bCompare_refl.
 assumption.
destruct IHt1 as [[k a] IHt].
exists (pair (Vcons _ false _ k) a).
assumption.
Qed.

Lemma trie_ext : forall n (ot1 ot2 : PatriciaTrie n), (forall k, get k ot1 = get k ot2) -> ot1 = ot2.
Proof.
assert (L1 : forall n (t : PatriciaTrieR n), ~(forall k : Bvector n, getR k t = None)).
 intros n t H.
 destruct (trieR_nonempty t) as [[k a] Hk].
 rewrite H in Hk.
 discriminate.
intros n [t1|] [t2|] Hot;
 [|elim (L1 _ t1)|elim (L1 _ t2);symmetry|reflexivity]; try firstorder.
apply f_equal.
revert Hot. 
change t2 with (eq_rec n PatriciaTrieR t2 n (eq_refl n)).
generalize (eq_refl n).
set (a:=n).
unfold a at 1 8 11.
revert t2.
induction t1; dependent inversion_clear t2;
(intros E; elim E using K_dec_set; try decide equality; simpl; intros Hot).
    generalize (Hot (Vnil _)); simpl; congruence.
   generalize (fun (k : Bvector n) => Hot (Vcons _ b _ k)).
   simpl.
   rewrite bCompare_refl.
   apply bCompare_elim; try (intros Hot'; elim (L1 _ t1); congruence).
   intros b1 Hot'.
   apply f_equal.
   apply (IHt1 p (refl_equal n)).
   assumption.
  elim (L1 _ (if b then p else p0)).
  intros k.
  generalize (Hot (Vcons _ (negb b) _ k)).
  case b; simpl; congruence.
 elim (L1 _ (if b then t1_1 else t1_2)).
 intros k.
 generalize (Hot (Vcons _ (negb b) _ k)).
 case b; simpl; congruence.
apply f_equal2.
 apply (IHt1_1 _ (refl_equal n)).
 intros k; apply (Hot (Vcons _ false _ k)).
apply (IHt1_2 _ (refl_equal n)).
intros k; apply (Hot (Vcons _ true _ k)).
Qed.

Lemma lens3 : forall n (k : Bvector n) ot nv1 nv2, set k (set k ot nv1) nv2 = set k ot nv2.
Proof.
intros n k ot nv1 nv2.
apply trie_ext.
intros k'.
case (vector_dec bool_dec k k').
 intros eq; rewrite <- eq; clear eq k'.
 rewrite !lens2; reflexivity.
intros Hk.
rewrite !get_indep; congruence.
Qed.

Lemma set_indep : forall n (k1 k2 : Bvector n) ot nv1 nv2, k1 <> k2 ->
 set k2 (set k1 ot nv1) nv2 = set k1 (set k2 ot nv2) nv1.
Proof.
intros n k1 k2 ot nv1 nv2 Hk.
apply trie_ext.
intros k3.
case (vector_dec bool_dec k3 k2); intros Hk'.
 rewrite Hk'; clear k3 Hk'.
 rewrite lens2, get_indep, lens2; congruence.
case (vector_dec bool_dec k3 k1); intros Hk''.
 rewrite Hk''; clear k3 Hk' Hk''.
 rewrite lens2, get_indep, lens2; congruence.
rewrite !get_indep; congruence.
Qed.

(* Note: the merkle hashing of the patricia tree should hash the keys with the values.
         In the case that they key is the hash of the value, then the key will be the hash of the value, so need not be included 
*)

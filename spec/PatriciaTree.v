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

Definition singleton n k v : PatriciaTrie n := Some (singletonR k v).

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

(*
Lemma lens3 : forall n (k : Bvector n) ot nv1 nv2, set k (set k ot nv1) nv2 = set k ot nv2.
*)
(* Note: the merkle hashing of the patricia tree should hash the keys with the values.
         In the case that they key is the hash of the value, then the key will be the hash of the value, so need not be included 
*)

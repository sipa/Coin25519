Require Import Bvector.

Definition bCompare (x y : bool) : comparison :=
match x, y with
| false, false => Eq
| false, true  => Lt
| true , false => Gt
| true , true  => Eq
end.

Section PatriciaTrie.

Variable A:Set.

Inductive PatriciaTrie : nat -> Set :=
| Tip : A -> PatriciaTrie 0
| Extend : bool -> forall n, PatriciaTrie n -> PatriciaTrie (S n)
| Branch : forall n, PatriciaTrie n -> PatriciaTrie n -> PatriciaTrie (S n).

Fixpoint singleton (n : nat) (k:Bvector n) (v:A) : PatriciaTrie n :=
match k in vector _ n return PatriciaTrie n with
| Vnil => Tip v
| Vcons r m k' => Extend r m (singleton _ k' v)
end.

Fixpoint get n (k:Bvector n) : PatriciaTrie n -> option A :=
match k in vector _ n return PatriciaTrie n -> option A with
| Vnil => fun t =>
  match t in PatriciaTrie m return if m then option A else unit with
  | Tip v => Some v
  | _ => tt
  end
| Vcons b n k' => fun t =>
  match t in PatriciaTrie m return match m with O => unit | S m' => (PatriciaTrie m' -> option A) -> option A end with
  | Tip _ => tt
  | Extend b0 m t0 => fun rec => if xorb b b0 then None else rec t0
  | Branch m t0 t1 => fun rec => if b then rec t1 else rec t0
  end (get n k')
end.

Let storeType n : Set := (option A * (option A -> option (PatriciaTrie n)))%type.

Definition map X Y (f : X -> Y) (st : option A * (option A -> X)) : option A * (option A -> Y) :=
let (stv, stg) := st in
(stv, fun oa => f (stg oa)).

Fixpoint lens n (k:Bvector n) : option (PatriciaTrie n) -> storeType n  :=
match k in vector _ n return option (PatriciaTrie n) -> storeType n with
| Vnil => fun ot =>
  match ot with 
  | None => (None, fun ov =>
    match ov with
    | None => None
    | Some v => Some (Tip v)
    end)
  | Some t =>
    match t in PatriciaTrie m return if m then storeType m else unit with
    | Tip v => (Some v, fun ov =>
      match ov with
      | None => None
      | Some v => Some (Tip v)
      end)
    | _ => tt
    end
  end
| Vcons b n k' => fun ot =>
  match ot with
  | None => (None, fun ov =>
    match ov with
    | None => None
    | Some v => Some (singleton _ (Vcons _ b n k') v)
    end)
  | Some t =>
    match t in PatriciaTrie m return match m with O => unit | S m' => Bvector m' -> (PatriciaTrie m' -> storeType m') -> storeType (S m') end with
    | Tip _ => tt
    | Extend b0 m t0 => fun k' rec =>
      match bCompare b b0 with
      | Lt => (None, fun ov =>
        match ov with
        | None => Some (Extend b0 m t0)
        | Some v => Some (Branch m (singleton m k' v) t0)
        end)
      | Eq => map _ _ (option_map (Extend b0 m)) (rec t0)
      | Gt => (None, fun ov =>
        match ov with
        | None => Some (Extend b0 m t0)
        | Some v => Some (Branch m t0 (singleton m k' v))
        end)
      end
    | Branch m t0 t1 => fun _ rec =>
      if b
      then map _ _ (option_map (Branch m t0)) (rec t1)
      else map _ _ (option_map (fun x => Branch m x t1)) (rec t0)
    end k' (fun t => lens n k' (Some t))
  end
end.


Require Import List Wf_nat NArith.

Definition Npower_nat (n:N) (m:nat) := iter_nat m N (fun x:N => n * x)%N 1%N.

Notation "n ^ m" := (Npower_nat n m).

Record SignatureStructure : Type :=
{ PubKeyType    : Set
; PrivKeyType   : Set
; SigType       : Set
; PubKeySigType : Set
(*; genPrivKey : ByteVector -> PrivKeyType *)
; getPubKey : PrivKeyType -> PubKeyType
; sign      : PrivKeyType -> N -> PubKeySigType
; verify    : PubKeyType -> SigType -> N -> bool
; recover   : PubKeySigType -> N -> PubKeyType
; _ : forall pk n, recover (sign pk n) n = getPubKey pk
}.

Variable SigKind : Set.

Axiom sigStructures : SigKind -> SignatureStructure.
Axiom EdDSA25519 : SigKind.

Section Script.

Inductive ExprType : Set :=
| Bool : ExprType
| Int : N -> ExprType
| PubKey : SigKind -> ExprType
| PrivKey : SigKind -> ExprType
| Sig : SigKind -> ExprType
| PubKeySig : SigKind -> ExprType
.

Definition Literal (ty:ExprType) : Set :=
match ty with
| Bool         => bool
| Int sz       => {n : N | n < sz}%N
| PubKey kd    => PubKeyType (sigStructures kd)
| PrivKey kd   => PrivKeyType (sigStructures kd)
| Sig kd       => SigType (sigStructures kd)
| PubKeySig kd => PubKeySigType (sigStructures kd)
end.

Inductive TransactionHashParameters : Set :=
| NoParametersYet : TransactionHashParameters
.

(* Goal: An expression langauge with quasi-linear space and time usage.
         To help reduce DoS *)

Inductive Expr : ExprType -> Set :=
| var : forall ty, Expr ty
| literal : forall ty, Literal ty -> Expr ty
| plus : forall bound : N, Expr (Int bound) -> Expr (Int bound) -> Expr (Int bound)
| mult : forall bound : N, Expr (Int bound) -> Expr (Int bound) -> Expr (Int bound)
| eq : forall ty, Expr ty -> Expr ty -> Expr Bool
| leq : forall ty, Expr ty -> Expr ty -> Expr Bool
| branch : forall ty, Expr Bool -> Expr ty -> Expr ty -> Expr ty
| sha256 : forall ty, Expr ty -> Expr (Int (2^256))
| sha512 : forall ty, Expr ty -> Expr (Int (2^512))
| transactionHash : TransactionHashParameters -> Expr (Int (2^256))
| keyRecovery : forall bound sig, Expr (Int bound) -> Expr (PubKeySig sig) -> Expr (PubKey sig)
| checkSig : forall bound sig, Expr (Int bound) -> Expr (PubKey sig) -> Expr (Sig sig) -> Expr Bool
| nonce : forall ty (n:N), (n < 2^256)%N -> Expr ty -> Expr ty
| unknownExpr : forall ty (n:N), (n < 2^256)%N -> Expr ty
.

(* A context is an ordered list of expression types *)
Definition Context := list ExprType.

Fixpoint ExprContext ty (e:Expr ty) : Context :=
match e with
| var ty => ty :: nil
| literal _ _ => nil
| plus _ e1 e2 => app (ExprContext _ e1) (ExprContext _ e2)
| mult _ e1 e2 => app (ExprContext _ e1) (ExprContext _ e2)
| eq _ e1 e2 => app (ExprContext _ e1) (ExprContext _ e2)
| leq _ e1 e2 => app (ExprContext _ e1) (ExprContext _ e2)
| branch _ e1 e2 e3 => app (ExprContext _ e1) (app (ExprContext _ e2) (ExprContext _ e3))
| sha256 _ e1 => ExprContext _ e1
| sha512 _ e1 => ExprContext _ e1
| transactionHash _ => nil
| keyRecovery _ _ e1 e2 => app (ExprContext _ e1) (ExprContext _ e2)
| checkSig _ _ e1 e2 e3 => app (ExprContext _ e1) (app (ExprContext _ e2) (ExprContext _ e3))
| nonce _ _ _ e1 => ExprContext _ e1
| unknownExpr _ _ _ => nil
end.

(* An environment is an ordered list of literals *)
Inductive Env : list ExprType -> Set :=
| emptyEnv : Env nil
| consEnv : forall ty tys, Literal ty -> Env tys -> Env (ty::tys)
.

(*Fixpoint Eval ty (e:Expr ty) (env : Env (ExprContext _ e)) : Literal ty.*)

End Script.

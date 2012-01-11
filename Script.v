Require Import Wf_nat.
Require Import NArith.

Definition Npower_nat (n:N) (m:nat) := iter_nat m N (fun x:N => n * x)%N 1%N.

Notation "n ^ m" := (Npower_nat n m).

Section Script.

Variable SigKind : Set.
Record SignatureStructure : Type :=
{ PubKeyType    : Set
; PrivKeyType   : Set
; SigType       : Set
; PubKeySigType : Set
  (* add signature operations *)
}.

Variable curve25519 : SigKind.
Variable sigStructures : SigKind -> SignatureStructure.

Inductive ExprType : Set :=
| Bool : ExprType
| Int : N -> ExprType
| PubKey : SigKind -> ExprType
| PrivKey : SigKind -> ExprType
| Sig : SigKind -> ExprType
| PubKeySig : SigKind -> ExprType.

Section Expr.
(* set of variable names *)
Variable (I:Set).

Inductive Expr : ExprType -> Set :=
| var : forall ty, I -> Expr ty
| boolLit : bool -> Expr Bool
| intLit : forall bound value : N, (value < bound)%N -> Expr (Int bound)
| pubKeyLit : forall sig, PubKeyType (sigStructures sig) -> Expr (PubKey sig)
| privKeyLit : forall sig, PrivKeyType (sigStructures sig) -> Expr (PrivKey sig)
| sigLit : forall sig, SigType (sigStructures sig) -> Expr (Sig sig)
| pubKeySigLit : forall sig, PubKeySigType (sigStructures sig) -> Expr (PubKeySig sig)
| plus : forall bound : N, Expr (Int bound) -> Expr (Int bound) -> Expr (Int bound)
(* only allow multiplication by a constant *)
| mult : forall bound value : N, (value < bound)%N -> Expr (Int bound) -> Expr (Int bound)
| eq : forall ty, Expr ty -> Expr ty -> Expr Bool
| branch : forall ty, Expr Bool -> Expr ty -> Expr ty -> Expr ty
| sha256 : forall ty, Expr ty -> Expr (Int (2^256))
| transactionHash : (* parameters *) Expr (Int (2^256))
| keyRecovery : forall bound sig, Expr (Int bound) -> Expr (PubKeySig sig) -> Expr (PubKey sig)
| checkSig : forall bound sig, Expr (Int bound) -> Expr (PubKey sig) -> Expr (Sig sig) -> Expr Bool
| unknownExpr : Expr (Int (2^256))
.

End Expr.

End Script.
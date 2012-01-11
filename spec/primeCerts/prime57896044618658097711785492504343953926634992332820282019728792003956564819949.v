Require Import PocklingtonRefl.

Set Virtual Machine.
Open Local Scope positive_scope.

Lemma prime273029885371 : prime 273029885371.
Proof.
 apply (Pocklington_refl
         (Pock_certif 273029885371 2 ((10501, 1)::(2,1)::nil) 20948)
        ((Proof_certif 10501 prime10501) ::
         (Proof_certif 2 prime2) ::
          nil)).
 exact_no_check (refl_equal true).
Qed.

Lemma prime57896044618658097711785492504343953926634992332820282019728792003956564819949: prime  57896044618658097711785492504343953926634992332820282019728792003956564819949.
apply (Pocklington_refl 

(SPock_certif 
57896044618658097711785492504343953926634992332820282019728792003956564819949
2
((74058212732561358302231226437062788676166966415465897661863160754340907, 1)::nil))
(
(Ell_certif
74058212732561358302231226437062788676166966415465897661863160754340907
202432877904592637622
((365840833263583138180149665669164550048897375058979,1)::nil)
74058212732561358302231226437062788676166966415465897661863160754319037
1102248
27
729)
::
(Ell_certif
365840833263583138180149665669164550048897375058979
32034796
((11420108099442341951550109057977693539328853,1)::nil)
0
5832
9
81)
::
(Ell_certif
11420108099442341951550109057977693539328853
208
((54904365862703567074762415821096255317109,1)::nil)
0
5832
9
81)
::
(SPock_certif 
54904365862703567074762415821096255317109
2
((415942165626542174808806180462850419069, 1)::nil))
::
(Ell_certif
415942165626542174808806180462850419069
6058180242
((68657938359593325359645641843,1)::nil)
400096337728019361924338022474293608214
399738282424149335022832531802435667237
260900388748715761425065301374208356733
52133767235549441136314596124741379674)
::
(Ell_certif
68657938359593325359645641843
27181884
((2525871214798564951081,1)::nil)
0
13310
11
121)
::
(SPock_certif 
2525871214798564951081
2
((1002329847142287679, 1)::nil))
::
(SPock_certif 
1002329847142287679
2
((7954998786843553, 1)::nil))
::
(Ell_certif
7954998786843553
29136
((273029885371,1)::nil)
0
192
4
16)
:: (Proof_certif 273029885371 prime273029885371) :: nil)).
exact_no_check (refl_equal true).
Time Qed.

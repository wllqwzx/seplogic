Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import language.
Require Import state.
Require Import util.

Fixpoint aeval (sto: store) (a: aexp): nat :=
match a with
| ANum n => n
| AId name => sto name
| APlus a1 a2 => (aeval sto a1) + (aeval sto a2)
| AMult a1 a2 => (aeval sto a1) * (aeval sto a2)
end.


Fixpoint beval (sto: store) (b: bexp): bool :=
match b with
| BTrue     => true
| BFalse    => false
| BEq a1 a2 => beq_nat (aeval sto a1) (aeval sto a2)
| BLe a1 a2 => leb (aeval sto a1) (aeval sto a2)
| BNot b1   => negb (beval sto b1)
| BAnd b1 b2 => andb (beval sto b1) (beval sto b2)
end.



Inductive big_step: command -> state -> ext_state -> Prop :=
| E_Skip  : forall stat,
              big_step CSkip stat (St stat)
| E_Ass   : forall sto h x a n, (aeval sto a) = n ->
              big_step (CAss x a) (sto,h) (St ((st_update sto x n),h))
| E_Seq   : forall c1 c2 st0 st1 opst,
              big_step c1 st0 (St st1) ->
              big_step c2 st1 opst ->
              big_step (CSeq c1 c2) st0 opst
| E_Seq_Ab: forall c1 c2 st0,
              big_step c1 st0 Abt ->
              big_step (CSeq c1 c2) st0 Abt
| E_IfTure: forall sto h opst b c1 c2,
              beval sto b = true ->
              big_step c1 (sto,h) opst ->
              big_step (CIf b c1 c2) (sto,h) opst
| E_IfFalse:forall b sto c1 c2 h opst,
              beval sto b = false ->
              big_step c2 (sto,h) opst ->
              big_step (CIf b c1 c2) (sto,h) opst
| E_WhileEnd : forall b sto h c,
                 beval sto b = false ->
                 big_step (CWhile b c) (sto, h) (St (sto, h))
| E_WhileLoop : forall sto h opst b c,
                  beval sto b = true ->
                  big_step (CSeq c (CWhile b c)) (sto, h) opst ->
                  big_step (CWhile b c) (sto, h) opst
| E_Cons : forall sto h a1 a2 n1 n2 x l,
              aeval sto a1 = n1 ->
              aeval sto a2 = n2 ->
              h l = None ->
              h (l + 1) = None ->
              big_step (CCons x a1 a2) (sto, h)
                       (St (st_update sto x l,
                            h_update (h_update h (l + 1) n2) l n1))
| E_Lookup : forall sto h x a1 n1 n2,
                aeval sto a1 = n1 ->
                h n1 = Some n2 ->
                big_step (CLookup x a1) (sto, h) (St (st_update sto x n2, h))
| E_Lookup_Ab : forall sto a1 n1 h x,
                   aeval sto a1 = n1 ->
                   h n1 = None ->
                   big_step (CLookup x a1) (sto, h) Abt
| E_Mutat : forall sto h a1 a2 n1 n2,
                  aeval sto a1 = n1 ->
                  aeval sto a2 = n2 ->
                  in_dom n1 h ->
                  big_step (CMutat a1 a2) (sto, h) (St (sto, h_update h n1 n2))
| E_Mutat_Ab : forall sto h a1 a2 n1,
                     aeval sto a1 = n1 ->
                     h n1 = None ->
                     big_step (CMutat a1 a2) (sto, h) Abt
| E_Dispose : forall sto h a1 n1,
                 aeval sto a1 = n1 ->
                 in_dom n1 h ->
                 big_step
                   (CDispose a1) (sto, h)
                   (St (sto, fun x => if eq_nat_dec x n1 then None else h x))
| E_Dispose_Ab : forall sto h a1 n1,
                    aeval sto a1 = n1 ->
                    h n1 = None ->
                    big_step (CDispose a1) (sto, h) Abt.












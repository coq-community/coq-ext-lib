Require Import Ascii.
Require Import String.
Require Import Coq.Program.Wf.
Require Import Omega.

Require Import ExtLib.Structures.Monoid.
Require Import Injection.

Class Show T :=
{ show : forall {m} {I:Injection ascii m} (M:Monoid m), T -> m }.

Fixpoint show_exact {m} {I:Injection ascii m} (M:Monoid m) (s:string) : m :=
  match s with
  | EmptyString => monoid_unit M
  | String a s' => monoid_plus M (inject a) (show_exact M s')
  end.

Instance bool_Show : Show bool :=
  { show _m _I M b := show_exact M (if b then "true"%string else "false"%string) }.
Instance ascii_Show : Show ascii :=
  { show _m _I M a :=
      monoid_plus M (inject "'"%char)
        (monoid_plus M (inject a)
          (inject "'"%char))
  }.
Instance string_Show : Show string :=
  { show _m _I M s :=
      monoid_plus M (inject """"%char)
        (monoid_plus M (show_exact M s)
          (inject """"%char))
  }.
Definition digit2char (n:nat) : ascii :=
  match n with
    | 0 => "0"%char
    | 1 => "1"%char
    | 2 => "2"%char
    | 3 => "3"%char
    | 4 => "4"%char
    | 5 => "5"%char
    | 6 => "6"%char
    | 7 => "7"%char
    | 8 => "8"%char
    | _ => "9"%char
  end.
Program Fixpoint nat_show {m} {I:Injection ascii m}
    (M:Monoid m) (n:nat) {measure n} : m :=
  if Compare_dec.le_gt_dec n 9 then
    inject (digit2char n)
  else
    let n' := NPeano.div n 10 in
    monoid_plus M (nat_show M n') (inject (digit2char (n - 10 * n'))).
Next Obligation.
  assert (NPeano.div n 10 < n) ; eauto.
  eapply NPeano.Nat.div_lt ; omega.
Defined.
Instance nat_Show : Show nat := { show m _I M := nat_show M}.

Section pair_Show.
  Context {A B} {AS:Show A} {BS:Show B}.
  Global Instance pair_Show : Show (A*B) :=
    { show _m _I M p :=
        let (a,b) := p in
        monoid_plus M (inject "("%char)
          (monoid_plus M (show M a)
            (monoid_plus M (inject ","%char)
              (monoid_plus M (show M b)
                (inject ")"%char))))
    }.
End pair_Show.

Section sum_Show.
  Context {A B} {AS:Show A} {BS:Show B}.
  Global Instance sum_Show : Show (A+B) :=
    { show _m _I M s :=
        let (tag, payload) :=
          match s with
          | inl a => (show_exact M "inl"%string, show M a)
          | inr b => (show_exact M "inr"%string, show M b)
          end
        in
        monoid_plus M (inject "("%char)
            (monoid_plus M tag
              (monoid_plus M (inject " "%char)
                (monoid_plus M payload
                  (inject ")"%char))))
    }.
End sum_Show.
(*
Examples:
Eval compute in (show Monoid_string_append (42,"foo"%string)).
Eval compute in (show Monoid_string_append_compose (inl true : bool+string) EmptyString).
*)

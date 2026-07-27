(*from https://github.com/DIJamner/pyrosome/blob/5ec226e35b75502a87d7663f637d2fa14eae6bb8/src/Utils/Default.v*)

From coqutil Require Import Map.Interface.

Section __.
  Context {A : Type}.

  Definition WithDefault := A.
  Existing Class WithDefault.

  Definition default {d : WithDefault} : A := d.

  Definition unwrap_or (d : A) oa : A :=
    match oa with None => d | Some a => a end.

  Definition unwrap_or_default `{WithDefault} oa : A :=
    unwrap_or default oa.

End __.
Arguments WithDefault : clear implicits.

#[export] Instance option_default {A} : WithDefault (option A) := None.
#[export] Instance list_default {A} : WithDefault (list A) := nil.
#[export] Instance nat_default : WithDefault nat := 0.
#[export] Instance map_default {key value} {mp : map.map key value} : WithDefault mp := map.empty.

From Stdlib Require Import String.
Local Open Scope string_scope.
#[export] Instance string_default : WithDefault string := "".

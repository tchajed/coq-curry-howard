(** * How does Coq work? *)

(** In this file, we'll explain Coq from the bottom-up, explaining what the
    primitives are and how many other aspects are derived from these primitives.

    To really emphasize this point, we use a [_CoqProject] file to disable loading
    Init from the Coq standard library. We'll define everything as we go.
 *)

(* ignore this; some things are really broken if we don't load some plugins *)
Require Coq.Init.Prelude.
Require Import Coq.Init.Notations.

(** First, types are the natural starting point to explain what Coq does have,
    since we'll need them to do anything else. Without Init, there are basically
    two types in Coq: [Prop] and [Type] (we're ignoring [Set] for now). We can
    make new types using inductive definitions, so let's add a couple:
*)

Inductive bool : Type :=
| true : bool
| false : bool
.

(** You may not have seen this sytax for inductive types, called GADT syntax in
    Haskell. For each constructor, we write out what it's type is. For simple
    inductive types these are all the same, but later we'll write inductive
    types where the type produced by different constructors might vary
    (specifically the arguments to the type). *)

(* this is the trivial type, analogous to Haskell and OCaml's empty tuple [()]
   or C's [void]. *)
Inductive unit : Type :=
| tt : unit
.

(** Ok, what about function types? Coq is based on dependent types, which just
    means that _types_ can depend on _terms_ (ordinary values like [nat]s and
    [bool]s, as well as functions and such).

    One way to understand this is the Barendregt or Lambda cube:

    - in all cases we'll consider, there are terms that depend on terms (these
      are just functions)
    - first, there are terms that depend on types (this is polymorphism or
      generics, like the identity function)
    - second, there are types that depend on other types (these are type
      operators, like the [list] type or tuples)
    - third, there are types that depend on terms (these are dependent types)

    An example of a dependent type is a vector type [Vector n] where [n] is the
    number of elements in the vector. *)

(** Coq only has the dependent function type built-in, which is written [forall
    (x:T), U]. To write down a function of that type, we use [fun (x:T) =>
    body]. We can already use this to write down the polymorphic identity
    function: *)

(** First, note that we write [(:T)] since the _type_ of the identity function
doesn't care what _value_ is passed. However, the definition certainly uses that
value, so we write [(x:T)]. *)
Definition id_really_explicit : forall (T:Type), forall (_:T), T :=
  fun (T:Type) => fun (x:T) => x.

(** It's common to write sequences of _binders_ (the things of the form
[(T:Type)]) that Coq has built-in syntax for them, which we will use to make
things easier to read: *)
Definition id : forall (T:Type) (_:T), T :=
  fun (T:Type) (x:T) => x.

(** Note that there's no special support for polymorphism. Instead, [id] is a
function that really takes a type and then arguments of that type. For example,
here's how we might apply [id]: *)

Definition id_true : bool := id bool true.

(* We can run [id_true] using evaluation: *)
Eval compute in id_true.

(** You've also seen one more type: [A -> B], the type of ordinary functions.
Turns out this isn't built-in to Coq, it's just a notation! An ordinary function
 type is a dependent function with no actual dependency: *)

Notation "A -> B" := (forall (_:A), B) : type_scope.

(** With dependent types there are an awful lot of type arguments to functions,
    for anything polymorphic. But we haven't had to deal with this because Coq
    has a feature called _implicit arguments_ to infer earlier arguments from
    later arguments, so that polymorphic functions behave more like they would
    in a non-dependently-typed language like Haskell.

    We'll use the [A -> B] notation and implicit arguments (the curly braces
    around binders) to make a nicer [id]: *)

Definition id' : forall {T:Type}, T -> T :=
  fun {T:Type} (x:T) => x.

(** Now we're ready to talk about theorems in Coq.

The big reveal is this: A Coq theorem statement is a type, and its proof is a
term of that type. (This is exactly the Curry-Howard correspondence.)

That is, for any theorem statement [P:Prop], we'll say [pf:P] is a proof of [P]
and that [P] is provable if [pf:P] exists.
 *)

(** I just said Coq theorems are types, but Coq actually uses [Prop] for the
    type of propositions and [Type] for other types. Propositions are basically
    types, but for reasons deeper than this explanation, Coq separates out
    propositional types from computational types, which are of type [Type]. You
    may treat them as the same thing for this document if you like.

    We'll first prove this the way you're used to, using Ltac.
  *)

Theorem P_implies_P : forall (P:Prop), P -> P.
Proof.
  intros P H.
  apply H.
Qed.

(** Now we'll prove it directly with a _proof term_, which is just a term: *)

Definition P_implies_P' : forall (P:Prop), P -> P :=
  fun (P:Prop) (H:P) => H.

(** This should look familiar - it's just the identity function! *)

(** Now to convince you that theorems really are the same as definition, we can
    take a look at [P_implies_P] and see that it's just a term: *)

Print P_implies_P.
Print P_implies_P'.

(** Ltac is a language for constructing proof terms imperatively. It lets us
    build up the proof incrementally, while seeing where we are, and it has
    powerful tools for inspecting the current goal and making progress. We can
    even build our own automation in Ltac to handle domain-specific problems.

    [lia] is one example of a domain-specific solver that we can use in Ltac,
    although it's not actually implemented in Ltac but as a plugin in OCaml.
 *)

(** Now we can give some high-level explanation of how we can prove more
interesting statements. The magic is all in inductive types in Coq, which can
produce all kinds of interesting dependencies. The first inductive type we'll
define is [True]. *)

Inductive True : Prop :=
| I : True.

(** This is analogous to [unit], but we just renamed some things and called it a
    [Prop] rather than a [Type]. It's easy to prove - just use the constructor [I] -
    and also tells you nothing if someone gives you a proof [H:True]. *)

(** Let's also define [False]: *)
Inductive False : Prop := .

(** There are no constructors, so it would seem we can't prove [False]. If we
could from no assumptions, then Coq would be _inconsistent_ as a logic (with the
above interpretation of propositions as theorems and terms as proofs) and you could prove
any theorem. That would make proofs in Coq extremely uninteresting.

As an aside, most other languages are inconsistent as logics. If you interpret a
Haskell type as a theorem, we can prove any theorem using an infinite loop:

<<
loop :: a
loop = loop
>>

We'll see how to produce a term of type [P -> False] in a bit. *)

(** The most interesting way to prove theorems in Coq is pattern matching
(closely tied with recursion for reasoning about recursive datatypes and
recursively defined theorem statements). Before going into a complicated pattern
match, let's look at a simple one over booleans. For exposition, I'll write this
 using Ltac (Coq doesn't care whether you use Ltac to prove theorems or write
definitions - they're the same thing, remember?). *)

Definition negb : bool -> bool.
  (* [intros b] produces [fun b => ...] in the "proof" term (it's not a proof in
  this case). *)
  intros b.
  (* Note that we could finish this "theorem" using [b], but that isn't the
  definition we want. If we only cared about [negb] as a proof of [bool -> bool]
  then we wouldn't care how it was proven, but we're actually planning on
  running it so its definition matters. *)
  destruct b.
  - (* this first case is where [b] is true. *)
    apply false.
  - (* this second case is where [b] is false. *)
    apply true.
    (* [Defined] is like [Qed], except that Coq will simplify [negb b] where
    possible. ([Qed] hides the definition of proofs, largely for performance
    reasons - real proof terms can be enormous. ) *)
Defined.

(** we can see the definition is what we would have written manually *)
Print negb.

(** Now for a more interesting proposition: the type [eq] of equality. (Yes,
this isn't built-in to Coq.) *)

Inductive eq (T:Type) (x:T) : T -> Prop :=
(* there's exactly one way to prove equality: reflexivity. *)
| eq_refl : eq T x x.

(** Now is a good time to remark that this definition does two things. The first
    is pretty clear: there's one way to prove [eq T x y], which is [eq_refl x :
    eq T x x]. What's less obvious is that we're also defining what we can do
    with a proof [H:eq T x y].

    The one thing we can do in Coq to make use of an inductive type is to
    pattern match on it. Pattern matching on a GADT like [eq T x y] tells us
    something about how it was constructed; in this case, informally speaking,
    it should tell us that [x] and [y] are "equal". Here's an example of using
    dependent pattern matching to prove a theorem, namely that the equality we
    just defined is symmetric. As before, we'll prove it using Ltac and then
    manually. I'll also give the association between the Ltac and the generated
    proof term. *)

Theorem eq_sym : forall (T:Type) (x y:T),
    eq T x y ->
    eq T y x.
Proof.
  intros T x y H.
  (* The [destruct] tactic starts a (dependent) pattern match *)
  destruct H.
  apply eq_refl.
Qed.

Print eq_sym.
(** The definition we wrote using Ltac is:
<<
eq_sym =
fun (T : Type) (x y : T) (H : eq T x y) =>
match H in (eq _ _ y0) return (eq T y0 x) with
| eq_refl _ _ => eq_refl T x
end
>>

This is a dependent pattern match over the _proof_ [H]. A dependent pattern
match in general looks like

<<
 match E as y in (T x1 ... xn) return U with
    | C z1 ... zm => B
    | ...
  end
>>

[E] is an expression in some inductive type [T] which has arguments [x1 ... xn]
(in our equality example [eq] is the inductive type and its arguments are [T x
y]). The overall type of the match is [U], where [x1 ... xn] are replaced by the
actual types from the type of [E], and with [y] replaced by [E].

The body of each clause in a match statement [B] is instead checked with the
type of the constructor [C]'s declared type (eg, [eq_refl] is declared to have
type [eq T x x]).

This is the only way Coq provides to extract information from the constructors
of an inductive type, but it's powerful enough to do almost anything you'd like.

My explanation is a bit informal, so if you really want to understand this, I'll
refer you to the excellent resource Certified Programming with Dependent Types
(CPDT), by Prof. Adam Chlipala: http://adam.chlipala.net/cpdt/html/MoreDep.html.
Especially look at "The One Rule of Dependent Pattern Matching in Coq".
 *)

(** Here's a particularly interesting example of dependent pattern matching that
    allows us to prove that a statement is false. First of all, how do we state
    that [P] is "false" (the informal notation)? We do this by proving the
    statement [P -> False]; you've now seen exactly what that means. We need a
    function that takes a proof [pf:P] and produces a value of type [False].
    Here's one way to do this, using dependent pattern matching.

 *)

Definition bool_constructors_differ : eq bool true false -> False :=
  fun (H:eq bool true false) =>
    match H in (eq _ _ b) return (match b with
                                  | true => True
                                  | false => False
                                  end) with
    | eq_refl _ _ => I
    end.

(** How does this work? The key is that the overall match statement's type
depends on the index to [eq]. That index [b] ends up as [false] from the type of
[H], and thus the overall match statement has type [False].

However, the body of the match statement (the [I]) is checked based on the type
of [eq_refl], which is [eq bool true true]. Substituting that in to the return
statement produces [True], and indeed [I:True].
*)

(** You don't have to write such compliciated terms yourself in Coq because
    tactics like [inversion] and [congruence] do them for you. These tactics
    don't produce such nice proof terms (they produce much larger ones) because
    they're written to be more general and systematic, handling a much wider
    range of inductive types. *)

(** As a final example, let's prove the principle of _explosion_, which says we
    can prove anything from [False]. We won't even use Ltac. *)

Definition explosion : forall (P:Prop), False -> P :=
  fun (P:Prop) (H:False) =>
    (* [False] has no constructors, we can annotate the return type with
       whatever we want and provide no cases. *)
    match H return P with
    end.

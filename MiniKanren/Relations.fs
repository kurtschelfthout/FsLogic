module MiniKanren.Relations

open Substitution
open Goal

type Atom<'a when 'a : equality> = AtomVar of LVar | Atom of 'a with
    static member Fresh() = AtomVar (Id())
    interface IUnify with
        member this.Var = match this with AtomVar v -> Some v | _ -> None
        member this.Occurs(_,_,_) = false
        member this.Unify(other,s) =
            let other = other :?> Atom<'a> //this is actually guaranteed, but the type system does not know it...
            match (this,other) with
            | (Atom a1,Atom a2) when a1 = a2 -> Some s
            | _ -> None

type LList<'a when 'a : equality> = ListVar of LVar | Nil | Cons of 'a * LList<'a> with
    static member Fresh() = ListVar (Id())
    interface IUnify with
        member this.Var = match this with ListVar v -> Some v | _ -> None
        member this.Occurs(_,_,_) = false
        member this.Unify(other,s) =
            let other = other :?> LList<'a>
            match (this,other) with
            | (Nil,Nil) -> Some s
            | (Cons (x,xs),Cons (y,ys)) when x = y -> unify xs ys s
            | _ -> None

///Tries goal an unbounded number of times.
let rec anyo goal =
    recurse (fun () -> goal ||| anyo goal)

///Goal that succeeds an unbounded number of times.
let alwayso = anyo (equiv (Atom true) (Atom true))

///Goal that fails an unbounded number of times.
let nevero = anyo (equiv (Atom true) (Atom false))

///Relates l,s and out so that l @ s = out
let inline appendo l s out = 
    let appendoF appendo (l,s,out) =
        equiv Nil l &&& equiv s out
        ||| let a,d = fresh(),fresh() in
            equiv (Cons (a,d)) l
            &&& let res = fresh() in
                appendo(d,s,res)
                &&& equiv (Cons (a,res)) out
    fix appendoF (l,s,out)

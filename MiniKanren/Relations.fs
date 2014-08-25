module MiniKanren.Relations

open Substitution
open Goal

type Atom<'a when 'a : equality> = AtomVar of Id | Atom of 'a with
    static member Fresh() = AtomVar (Id())
    interface IUnify with
        member this.Var = match this with AtomVar v -> Some v | _ -> None
        member this.Occurs(_,_,_) = false
        member this.Unify(other,s) =
            let other = other :?> Atom<'a> //this is actually guaranteed, but the type system does not know it...
            match (this,other) with
            | (Atom a1,Atom a2) when a1 = a2 -> Some s
            | _ -> None
        member this.Walk s = upcast this

type LList<'a when 'a : equality and 'a :> IUnify> = ListVar of Id | Nil | Cons of 'a * LList<'a> with
    static member Fresh() = ListVar (Id())
    static member FromSeq s = List.foldBack (curry Cons) (s |> Seq.toList) Nil
    interface IUnify with
        member this.Var = match this with ListVar v -> Some v | _ -> None
        member this.Occurs(_,_,_) = false
        member this.Unify(other,s) =
            let other = other :?> LList<'a>
            match (this,other) with
            | (Nil,Nil) -> Some s
            | (Cons (x,xs),Cons (y,ys)) -> unify x y s |> Option.bind (unify xs ys)
            | _ -> None
        member this.Walk s =
            match this with
            | Cons (x,xs) -> upcast Cons(walkMany x s, walkMany xs s)
            | _ -> upcast this
///Tries goal an unbounded number of times.
let rec anyo goal =
    recurse (fun () -> goal ||| anyo goal)

///Goal that succeeds an unbounded number of times.
let alwayso = anyo (equiv (Atom true) (Atom true))

///Goal that fails an unbounded number of times.
let nevero = anyo (equiv (Atom true) (Atom false))

///Relates l,s and out so that l @ s = out
let rec appendo xs ys out = 
    recurse (fun () ->
        equiv Nil xs &&& equiv ys out
        ||| let x,xs',res = fresh(),fresh(),fresh() in
            equiv (Cons (x,xs')) xs
            &&& appendo xs' ys res
            &&& equiv (Cons (x,res)) out)

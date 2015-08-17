module MiniKanren.Relations

open Substitution
open Goal

type Atom<'a> = Val of 'a | VarA with
    static member Fresh() = VarA
    interface IUnifiable with
        member x.Unify(arg1: IUnifiable): Subst option = failwith "Not implemented yet"
        member x.Var: VarName option = failwith "Not implemented yet"
        member x.Walk: (IUnifiable list -> IUnifiable) * IUnifiable list = failwith "Not implemented yet"
    
type LList<'a> = Nil | Cons of 'a * LList<'a> | VarL with
    static member Fresh() = VarL
    static member ($)(a,l) = Cons (a,l)
    //static member (++)(Cons (a,l),l2) = Cons (a,l2)
    interface IUnifiable with
        member x.Unify(arg1: IUnifiable): Subst option = failwith "Not implemented yet"
        member x.Var: VarName option = failwith "Not implemented yet"
        member x.Walk: (IUnifiable list -> IUnifiable) * IUnifiable list = failwith "Not implemented yet"

let (~+) a = Val a

///Tries goal an unbounded number of times.
let rec anyo goal =
    recurse (fun () -> goal ||| anyo goal)

///Goal that succeeds an unbounded number of times.
let alwayso = anyo (equiv +true +true)

///Goal that fails an unbounded number of times.
let nevero = anyo (equiv +true +false)

///Non-relational. The given goal succeeds at most once.
let onceo goal = condu [ [ goal ] ]

//---lists----

///Relates l with the empty lst.
let emptyo l = equiv l Nil

///Relates h and t with the list l such that (h::t) = l.
let conso h t (l:LList<'a>) = equiv (Cons (h,t)) l

///Relates h with the list l such that (h::_) = l.
let heado h l =
    let t = fresh()
    conso h t l

///Relates t with the list l such that (_::t) = l.
let inline tailo t l =
    let h = fresh()
    conso h t l

///Relates l,s and out so that l @ s = out
let rec inline appendo l s out = 
    emptyo l &&& equiv s out
    ||| let a,d = fresh(),fresh() in
        conso a d l
        &&& let res = fresh() in
            conso a res out
            &&& recurse (fun () -> appendo d s res)

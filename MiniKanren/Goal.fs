module MiniKanren.Goal

open MiniKanren.Substitution
open System

type Stream<'a> =
    | MZero
    | Unit of 'a
    | Choice of 'a * Stream<'a>
    | Inc of Lazy<Stream<'a>>


//note: minikanren says: A goal is a function maps a substitution to an
//ordered sequence of zero or more values. These are _almost always_ substituions.
type Goal<'a> = Subst -> Stream<'a>

let equiv u v : Goal<_> =
    fun a -> 
        unify u v a
        |> Option.map Unit
        |> Option.defaultTo MZero

let equivNoCheck u v : Goal<_> =
    fun a -> 
        unifyNoCheck u v a
        |> Option.map Unit
        |> Option.defaultTo MZero

let rec mplus a b =
    match a with
    | MZero -> b
    | Unit a -> Choice (a,b)
    | Choice(a,b') -> Choice (a,mplus b b') //interesting - interleaving of the results here
    | Inc a' -> Inc (lazy mplus b a'.Value) 

let rec bind s g =
    match s with
    | MZero -> MZero
    | Unit a -> g a
    | Choice (a,b) -> mplus (g a) (bind b g)
    | Inc f -> Inc (lazy bind f.Value g)

let rec mplusMany streams =
    match streams with
    | [] -> MZero
    | [g] -> g
    | (g::gs) -> mplus g (mplusMany gs)

let rec bindMany str goals =
    match goals with
    | [] -> str
    | (g::gs) -> bindMany (bind str g) gs

let conde (goals:#seq<Goal<_> * #seq<Goal<_>>>) : Goal<_> =
    fun a -> 
        Inc (lazy (mplusMany (goals |> Seq.map (fun (g,gs) -> (bindMany (g a) gs)) |> Seq.toList) ))

let exist f =
    fun a ->
        Inc (lazy (let (g0::gs)  = f ()
                   bindMany (g0 a) gs))

let (=>) g1 g2 = 
    //let thenS g1 (g2:Lazy<_>) = fun a -> Inc (lazy (bind (g1 a) g2.Value))
    let thenS g1 g2 = fun a -> Inc (lazy (bind (g1 a) g2))
    thenS g1 g2

let (.|) g1 g2 =
    let orS g1 g2 = fun a -> Inc (lazy (mplus (g1 a) (g2 a)))
    orS g1 g2

let (.&) g1 g2 = 
    let res = fun a -> bind (g1 a) g2
    res

let rec fix f x = fun a -> Inc (lazy (f (fix f) x a))

let rec take n f =
    if n = 0 then 
        []
    else
        match f with
        | MZero -> []
        | Inc (Lazy s) -> take n s
        | Unit a -> [a]
        | Choice(a,f) ->  a :: take (n-1) f

let run n f =
    //let's hack this in
    Inc (lazy (let x = Var <| new Var() //"_goal_"
               let g0  = f x
               bind (g0 Subst.Empty) (Unit << reify x)))
    |> take n

//this doesn't work because the x passed into the reify is not the real var - that is only
//given by exist. And we can't bind the reify inside the exist because then the types don't match.
//Sucks.
//    let g = bind ((exist [x] (fun x -> f x)) Subst.Empty) (reify x >> Unit)
//    take n g

let newVar() = Var (new Var())

//impure operators
let project (v:Term) (f:obj -> Goal<_>) : Goal<_> =
    fun s -> 
        printfn "s=%A" s
        //assume atom here..otherwise fail
        let (Atom x) = walkMany v s
        printfn "x=%A" x
        f x s


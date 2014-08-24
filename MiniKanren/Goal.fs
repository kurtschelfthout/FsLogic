module MiniKanren.Goal

open MiniKanren.Substitution
open System

//a good explantion of the need for all these cases is in the uKanren paper.
type Stream<'a> =
    | MZero
    | Unit of 'a
    | Choice of 'a * Stream<'a>
    | Inc of Lazy<Stream<'a>>

//A goal is a function that maps a substitution to an
//ordered sequence of zero or more values. These are _almost always_ substitutions.
type Goal = Subst -> Stream<Subst>

let equiv u v : Goal =
    fun a -> 
        unify u v a
        |> Option.map Unit
        |> Option.defaultTo MZero

let equivNoCheck u v : Goal =
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

let conde (goals:#seq<Goal * list<Goal>>) : Goal =
    fun a -> 
        Inc (lazy (mplusMany (goals |> Seq.map (fun (g,gs) -> (bindMany (g a) gs)) |> Seq.toList) ))

//let (=>) g1 g2 = 
//    fun a -> bind (g1 a) g2

let (|||) g1 g2 =
    fun a -> mplus (g1 a) (g2 a)

let (&&&) g1 g2 = 
    fun a -> bind (g1 a) g2

let recurse fg =
    fun a -> Inc (lazy fg() a)

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
    Inc (lazy (let x = Var <| new Id() 
               let g0  = f x
               bind (g0 Subst.Empty) (Unit << reify x)))
    |> take n

//this doesn't work because the x passed into the reify is not the real var - that is only
//given by exist. And we can't bind the reify inside the exist because then the types don't match.
//Sucks.
//    let g = bind ((exist [x] (fun x -> f x)) Subst.Empty) (reify x >> Unit)
//    take n g

let fresh() = Var (new Id())

//impure operators
let project (v:Term) (f:obj -> Goal) : Goal =
    fun s -> 
        //assume atom here..otherwise fail
        let (Atom x) = walkMany v s
        f x s

//type G =
//    static member inline Eq(t1:Term, t2:Term) = equiv t1 t2
//    static member inline Eq(t1:Term, t2:'a) = equiv t1 (Atom t2)
//    static member inline Eq(t1:'a, t2:Term) = equiv (Atom t1) t2
//    static member inline Eq(t1:'a, t2:'b) = equiv (Atom t1) (Atom t2)
//    static member Eq(t1:Term, t2:seq<'a>) = equiv t1 (Atom t2)
//    static member Eq(t1:seq<'a>, t2:Term) = equiv (Atom t1) t2
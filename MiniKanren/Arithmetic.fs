module MiniKanren.Arithmetic

open Substitution
open Goal

//let buildNumber n =
//    let (|Even|_|) n = if n % 2 = 0 then Some n else None
//    let cons a b = a :: b
//    let rec helper k n =
//        match n with
//        | 0 -> k []
//        | Even n -> helper (fun k' -> k (cons 0)) (n/2)
//        | _ -> helper (fun k' -> k (cons 1)) ((n-1)/2)
//    let r = helper id n 
//    r

let poso n = 
    equiv n <@ %__()::%__() @>

let ``>1o`` n =
    equiv n <@ %__()::%__()::%__() @>

let private truthTable x y r =
    List.map (fun (a,b,c) -> [equiv <@ %x,%y,%r @> <@ a,b,c @>])
    >> conde

let bitAndo x y r =
    [   (0,0,0)
        (1,0,0)
        (0,1,0)
        (1,1,1)
    ] |> truthTable x y r

let bitXoro x y r =
    [   (0,0,0)
        (0,1,1)
        (1,0,1)
        (1,1,0)
    ] |> truthTable x y r
    
let halfAddero x y r c =
    bitXoro x y r
    &&& bitAndo x y c

let fullAddero b x y r c =
    let (w,xy,wz) = fresh3()
    all [ halfAddero x y w xy
          halfAddero w b r wz
          bitXoro xy wz c ]

///not really matche: just calls equiv with the first argument 
///on all the heads of a given list; joining them in a conde.
let matche pat (goals:(_ * Goal list) list) = 
    goals
    |> List.map (fun (h,l) -> equiv pat h :: l)
    |> conde

let rec addero d n m r : Goal =
    recurse (fun () -> 
    matche <@ %d,%n,%m @> 
        [ <@ (0    , %__(), []    ) @>, [equiv n r]
          <@ (0    , []   , %__() ) @>, [equiv m r; poso m]
          <@ (1    , %__(), []    ) @>, [addero <@ 0 @> n <@ [1] @> r]
          <@ (1    , []   , %__() ) @>, [poso m; addero <@ 0 @> <@ [1] @> m r]
          <@ (%__(), [1]  , [1]   ) @>, (let a,c = fresh2() in [equiv <@ [%a; %c] @> r; fullAddero d <@ 1 @> <@ 1 @> a c ])
          <@ (%__(), [1]  , %__() ) @>, [genAddero d n m r]
          <@ (%__(), %__(), [1]   ) @>, [``>1o`` n; ``>1o`` r; addero d <@ [1] @> n r]
          <@ (%__(), %__(), %__() ) @>, [``>1o`` n; genAddero d n m r]
        ])
and genAddero d n m r =
    let a,b,c = fresh3()
    let x,y,z = fresh3()
    let e = fresh()
    all [ equiv <@ %n, %m, %r @> <@ %a::%x, %b::%y, %c::%z @>
          poso y; poso z
          fullAddero d a b c e
          addero e x y z ]

let pluso n m k : Goal = addero <@ 0 @> n m k


    
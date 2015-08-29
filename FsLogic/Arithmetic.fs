module FsLogic.Arithmetic

open Substitution
open Goal
open Relations

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
    n *=* cons __ __

let ``>1o`` n =
    n *=* cons __ (cons __ __)

let private truthTable x y r =
    List.map (fun (a,b,c) -> [ (x,y,r) *=* (prim a, prim b, prim c)])
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
    let (w,xy,wz) = fresh()
    all [ halfAddero x y w xy
          halfAddero w b r wz
          bitXoro xy wz c ]

let rec addero d n m r : Goal =
    let p = prim
    let l1l = cons 1Z nil //[1]
    recurse (fun () -> 
    matche (d,n,m)
        [ (0Z  , __ , nil) ->> [n *=* r]
          (0Z  , nil, __ ) ->> [m *=* r; poso m]
          (1Z  , __ , nil) ->> [addero 0Z n l1l r]
          (1Z  , nil, __ ) ->> [poso m; addero 0Z l1l m r]
          (__  , l1l, l1l) ->> (let a,c = fresh() in [(cons a (cons c nil)) *=* r; fullAddero d 1Z 1Z a c ])
          (__  , l1l, __ ) ->> [genAddero d n m r]
          (__  , __ , l1l) ->> [``>1o`` n; ``>1o`` r; addero d l1l n r]
          (__  , __ , __ ) ->> [``>1o`` n; genAddero d n m r]
        ])

and genAddero d n m r =
    let a,b,c = fresh()
    let x,y,z = fresh()
    let e = fresh()
    all [ (n, m, r) *=* (cons a x, cons b y, cons c z)
          poso y; poso z
          fullAddero d a b c e
          addero e x y z ]

let pluso n m k : Goal = addero 0Z n m k
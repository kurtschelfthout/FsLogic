#I @"bin\Debug\netcoreapp2.0"
#r "FsLogic.dll"
//#r "Unquote.dll"
open FsLogic
open FsLogic.Goal
open FsLogic.Substitution
open FsLogic.Arithmetic
open FsLogic.Relations

let res = run -1 (fun q -> removeo 2Z ~~[2] q)

let (Det l) = res.[0]

l.GetType()

//r = Det []

let s = Det []
let l : obj = box []
let l1 : obj = [1] |> List.tail |> box


l = l1

[ Det [] ] = [ Det [] ]



let res = runShow 10 (fun q -> let d,n,m = fresh3()  in addero d n m q)
printfn "%s" res

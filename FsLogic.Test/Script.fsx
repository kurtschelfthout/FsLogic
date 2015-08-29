#I @"bin\Debug"
#r "FsLogic.dll"
#r "Unquote.dll"

open FsLogic.Goal
open FsLogic.Substitution
open FsLogic.Arithmetic

let res = runShow 10 (fun q -> let d,n,m = fresh3()  in addero d n m q)
printfn "%s" res

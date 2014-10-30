#I @"bin\Debug"
#r "MiniKanren.dll"
#r "Unquote.dll"

open MiniKanren.Goal
open MiniKanren.Substitution
open MiniKanren.Arithmetic

let res = runShow 10 (fun q -> let d,n,m = fresh3()  in addero d n m q)
printfn "%s" res
